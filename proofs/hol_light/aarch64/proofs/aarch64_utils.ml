(*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

needs "common/mldsa_specs.ml";;

(* ------------------------------------------------------------------------- *)
(* Symbolic execution until target PC is reached.                            *)
(* ------------------------------------------------------------------------- *)

let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read PC some_state = some_value`) in
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually arm (\s'. P) some_state` goal in
    insts |> rev_assoc `P: bool` |> conjuncts |> find is_pc_condition in
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with _ -> None in
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  let TARGET_PC_REACHED_TAC target_pc = fun (asl, w) ->
    if has_matching_pc_assumption asl target_pc then ALL_TAC (asl, w)
    else NO_TAC (asl, w) in
  let rec core n (asl, w) =
    (TARGET_PC_REACHED_TAC target_pc ORELSE (f n THEN core (n + 1))) (asl, w)
  in core n (asl, w);;

(* ========================================================================= *)
(* SIMD simplification: subword extraction + numeric reduction + folding.    *)
(* ========================================================================= *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

(* ========================================================================= *)
(* Parametric infrastructure for d-bit packed coefficients (SIMD).           *)
(* Supports d=18 (GAMMA1=2^17) and d=20 (GAMMA1=2^19).                      *)
(* ========================================================================= *)

(* Convert MOD/DIV expressions to word_subword of (16*d)-bit word *)
let mk_base_simps d =
  let total = 16 * d in
  let rem = total - 256 in
  let total_ty = mk_finty (Num.num_of_int total) in
  let rem_ty = mk_finty (Num.num_of_int rem) in
  let mod_128 = CONV_RULE NUM_REDUCE_CONV (prove(
    inst [total_ty, `:N`]
      `word (t MOD 2 EXP 128) : 128 word =
       word_subword (word t : N word) (0, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    REWRITE_TAC[EXP; DIV_1; MOD_MOD_REFL; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    MP_TAC (SPECL [`t:num`; `2`; mk_small_numeral total; `128`] MOD_MOD_EXP_MIN) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let div_128_mod_128 = CONV_RULE NUM_REDUCE_CONV (prove(
    inst [total_ty, `:N`]
      `word ((t DIV 2 EXP 128) MOD 2 EXP 128) : 128 word =
       word_subword (word t : N word) (128, 128)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_128] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[ARITH_RULE `MIN 128 128 = 128`; MOD_MOD_REFL] THEN
    REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV)) in
  let div_256 = CONV_RULE NUM_REDUCE_CONV (prove(
    inst [total_ty, `:N`; rem_ty, `:M`]
      `word (t DIV 2 EXP 256) : M word =
       word_subword (word t : N word) (256, dimindex(:M))`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL])) in
  [mod_128; div_128_mod_128; div_256];;

(* Split ncoeffs d-bit coefficients into chunks of chunk_size *)
let mk_split_theorem d ncoeffs chunk_size =
  let total = d * chunk_size in
  let nchunks = ncoeffs / chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  prove(
    subst [mk_small_numeral ncoeffs, `ncoeffs:num`;
           mk_small_numeral chunk_size, `cs:num`;
           mk_small_numeral nchunks, `nc:num`]
    (inst [d_ty, `:D`; total_ty, `:T`]
      `!(l: (D word) list). LENGTH l = ncoeffs ==>
         num_of_wordlist l = num_of_wordlist (MAP ((word:num->T word) o num_of_wordlist)
           (list_of_seq (\i. SUB_LIST (cs * i, cs) l) nc))`),
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN (subst [mk_small_numeral ncoeffs, `n:num`]
      (inst [d_ty, `:D`] `LENGTH (l : (D word) list) = n`)) (fun th ->
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [MATCH_MP (CONV_RULE NUM_REDUCE_CONV
           (ISPECL [mk_small_numeral chunk_size; mk_small_numeral nchunks;
                    `l:'a list`] SUBLIST_PARTITION)) th]
       THEN ASSUME_TAC th) THEN
    IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (ISPECL [inst [d_ty, `:D`] `ll: ((D word) list) list`;
               mk_small_numeral chunk_size]
        (INST_TYPE [d_ty, `:N`; total_ty, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
    CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
    ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
    ARITH_TAC);;

(* Extract individual d-bit coefficients from (d*chunk_size)-bit word *)
let mk_subword_cases d chunk_size =
  let total = d * chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  let arith_simp =
    let lhs = mk_eq(mk_small_numeral total,
                mk_comb(mk_comb(`( * ):num->num->num`,
                  mk_small_numeral d), `n:num`)) in
    let rhs = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    ARITH_RULE (mk_eq(lhs, rhs)) in
  let meson_simp =
    let n_eq = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    let k_lt_n = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`), `n:num`) in
    let k_lt_cs = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`),
                    mk_small_numeral chunk_size) in
    MESON[] (mk_eq(mk_conj(n_eq, k_lt_n), mk_conj(n_eq, k_lt_cs))) in
  let base =
    let th = INST_TYPE [total_ty, `:KL`; d_ty, `:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
    let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
    REWRITE_RULE[arith_simp; meson_simp] th in
  let mk k =
    let th = SPEC (mk_small_numeral k)
      (SPEC (inst [d_ty, `:L`] `ls:(L word)list`) base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0 -- (chunk_size - 1));;

(* ========================================================================= *)
(* zunpack lane conversion for TBL + USHL + AND + SUB pipeline.              *)
(* ========================================================================= *)

let ZUNPACK_LANE_CONV d i tm =
  let gamma1 = 1 lsl (d - 1) in
  let word_bits = 16 * d in
  match find_word_subterm_n word_bits tm with
    | Some t_var ->
        let d_ty = mk_finty (Num.num_of_int d) in
        let t_ty = mk_finty (Num.num_of_int word_bits) in
        let goal = mk_eq(tm,
          subst [mk_small_numeral (d*i), `pos:num`;
                 mk_small_numeral d, `bw:num`;
                 mk_small_numeral gamma1, `g:num`;
                 t_var, mk_var("t", mk_type("word",[t_ty]))]
            (inst [d_ty, `:B`; t_ty, `:T`]
              `word_sub (word g : 32 word)
                        (word_zx (word_subword (t : T word) (pos,bw) : B word))`)) in
        WORD_BLAST goal
    | None -> failwith ("no " ^ string_of_int word_bits ^ "-bit word found");;

let ZUNPACK_128_CONV d tm =
  tryfind (fun base_i ->
    RAND_CONV (BINOP_CONV_N 2 (fun j -> ZUNPACK_LANE_CONV d (base_i + j))) tm
  ) [0; 4; 8; 12];;

let SIMP_ZUNPACK_TAC d zunpack_correct =
  let zunpack_const =
    fst(strip_comb(rhs(snd(strip_forall(concl zunpack_correct))))) in
  let already_processed tm =
    can (find_term ((=) zunpack_const)) tm in
  RULE_ASSUM_TAC (fun th ->
    if already_processed (concl th) then th
    else CONV_RULE (TRY_CONV (ZUNPACK_128_CONV d) THENC
                    TRY_CONV (ONCE_REWRITE_CONV [zunpack_correct])) th);;
