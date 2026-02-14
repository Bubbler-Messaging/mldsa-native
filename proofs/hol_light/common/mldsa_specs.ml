(*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* Architecture-independent specifications for ML-DSA                        *)
(* ========================================================================= *)

(* ========================================================================= *)
(* zunpack: gamma1 - x unpacking for polyz                                   *)
(*                                                                           *)
(* zunpack_d maps a d-bit packed coefficient x in [0, 2^d - 1] to           *)
(* gamma1 - x in [-(gamma1-1), gamma1], where gamma1 = 2^(d-1).             *)
(* ========================================================================= *)

(* --- zunpack17: GAMMA1 = 2^17, 18-bit packed coefficients --- *)

let zunpack17 = new_definition
 `zunpack17 (x:(18)word) : (32)word =
  word_sub (word(2 EXP 17)) (word_zx x)`;;

let ZUNPACK17_CORRECT = prove(
  `!x:(18)word.
    word_sub (word 131072 : 32 word)
             (word_zx (x : 18 word) : 32 word) = zunpack17 x`,
  REWRITE_TAC[zunpack17] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZUNPACK17_IVAL = prove(
 `!x:(18)word. ival(zunpack17 x) = &(2 EXP 17) - &(val x)`,
  GEN_TAC THEN REWRITE_TAC[zunpack17] THEN
  SUBGOAL_THEN `word_zx (x:18 word) : 32 word = word(val x)` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
   MP_TAC(ISPEC `x:18 word` VAL_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN SIMP_TAC[MOD_LT];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:18 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK17_BOUND = prove(
 `!x:(18)word. --(&(2 EXP 17) - &1) <= ival(zunpack17 x) /\
               ival(zunpack17 x) <= &(2 EXP 17)`,
  GEN_TAC THEN REWRITE_TAC[ZUNPACK17_IVAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:18 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK17_MAP_BOUND = prove(
 `!l:(18 word) list. !i. i < LENGTH l ==>
    --(&(2 EXP 17) - &1) <= ival(EL i (MAP zunpack17 l)) /\
    ival(EL i (MAP zunpack17 l)) <= &(2 EXP 17)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
  REWRITE_TAC[ZUNPACK17_BOUND]);;

(* --- zunpack19: GAMMA1 = 2^19, 20-bit packed coefficients --- *)

let zunpack19 = new_definition
 `zunpack19 (x:(20)word) : (32)word =
  word_sub (word(2 EXP 19)) (word_zx x)`;;

let ZUNPACK19_CORRECT = prove(
  `!x:(20)word.
    word_sub (word 524288 : 32 word)
             (word_zx (x : 20 word) : 32 word) = zunpack19 x`,
  REWRITE_TAC[zunpack19] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZUNPACK19_IVAL = prove(
 `!x:(20)word. ival(zunpack19 x) = &(2 EXP 19) - &(val x)`,
  GEN_TAC THEN REWRITE_TAC[zunpack19] THEN
  SUBGOAL_THEN `word_zx (x:20 word) : 32 word = word(val x)` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
   MP_TAC(ISPEC `x:20 word` VAL_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN SIMP_TAC[MOD_LT];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:20 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK19_BOUND = prove(
 `!x:(20)word. --(&(2 EXP 19) - &1) <= ival(zunpack19 x) /\
               ival(zunpack19 x) <= &(2 EXP 19)`,
  GEN_TAC THEN REWRITE_TAC[ZUNPACK19_IVAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:20 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK19_MAP_BOUND = prove(
 `!l:(20 word) list. !i. i < LENGTH l ==>
    --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
    ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
  REWRITE_TAC[ZUNPACK19_BOUND]);;

(* ========================================================================= *)
(* Helper lemmas: list operations                                            *)
(* ========================================================================= *)

let EL_SUB_LIST = prove(
 `!l:'a list. !i k n. i < n /\ k + n <= LENGTH l
   ==> EL i (SUB_LIST (k, n) l) = EL (k + i) l`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LT; SUB_LIST_CLAUSES; ADD_CLAUSES] THENL [
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
      REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `0`; `n':num`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EL; TL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`; `n':num`; `SUC n''`]) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let EL_SUB_LIST_CONV len_thm tm =
  let i_tm,sublist_tm = dest_comb tm in
  let el_const,i = dest_comb i_tm in
  let sublist_pair,ls = dest_comb sublist_tm in
  let sublist_const,pair_tm = dest_comb sublist_pair in
  let base,len = dest_pair pair_tm in
  let i_num = dest_numeral i and
      len_num = dest_numeral len in
  if i_num >= len_num then failwith "EL_SUB_LIST_CONV: index out of bounds" else
  let th1 = ISPECL [ls; i; base; len] EL_SUB_LIST in
  let th2 = REWRITE_RULE[len_thm] th1 in
  let th3 = MP th2 (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl th2))))) in
  CONV_RULE (RAND_CONV (LAND_CONV NUM_ADD_CONV)) th3;;

let LENGTH_SUB_LIST_0 = prove
 (`!n (l:'a list). n <= LENGTH l ==> LENGTH (SUB_LIST (0, n) l) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_ARITH_TAC);;

let SUB_LIST_SUB_LIST_0 = prove(
 `!k n m (l:'a list). k + n <= m /\ m <= LENGTH l
   ==> SUB_LIST (k, n) (SUB_LIST (0, m) l) = SUB_LIST (k, n) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; SUB_0] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n' < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (ISPECL [`SUB_LIST (0,m) l:'a list`; `n':num`; `k:num`; `n:num`] EL_SUB_LIST) THEN
  MP_TAC (ISPECL [`l:'a list`; `n':num`; `k:num`; `n:num`] EL_SUB_LIST) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
  SUBGOAL_THEN `k + n <= LENGTH (l:'a list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k + n <= MIN m (LENGTH (l:'a list))` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (ISPECL [`l:'a list`; `k + n':num`; `0`; `m:num`] EL_SUB_LIST) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let SUB_LIST_SPLIT_EQ = prove
 (`!n r (l:'a list). n + r = LENGTH l
   ==> APPEND (SUB_LIST (0, n) l) (SUB_LIST (n, r) l) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`l:'a list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC[ADD_SUB2]);;

let APPEND_ITLIST_APPEND_NIL = prove
 (`!(l:('a list) list) (x:'a list). APPEND (ITLIST APPEND l []) x = ITLIST APPEND l x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; APPEND] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN ASM_REWRITE_TAC[]);;

let LIST_OF_SEQ_EQ = prove
 (`!(f:num->'a) g n. (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[list_of_seq] THEN
  DISCH_TAC THEN BINOP_TAC THENL [
    FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC
  ]);;

let SUBLIST_PARTITION = prove
 (`!r s (l:'a list). LENGTH l = r * s ==>
       l = ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) l) s) []`,
  GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[MULT_CLAUSES; list_of_seq; ITLIST; LENGTH_EQ_NIL];
    REWRITE_TAC[list_of_seq; ITLIST_EXTRA; APPEND_NIL] THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `SUB_LIST (0, r * s) l =
       ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) (SUB_LIST (0, r * s) l)) s) []:'a list`
      ASSUME_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LENGTH_SUB_LIST_0 THEN ASM_ARITH_TAC;
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `list_of_seq (\i. SUB_LIST (r * i, r) (SUB_LIST (0, r * s) l):'a list) s =
       list_of_seq (\i. SUB_LIST (r * i, r) l) s`
      ASSUME_TAC THENL [
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUB_LIST_SUB_LIST_0 THEN CONJ_TAC THENL [
        REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `APPEND (SUB_LIST (0, r * s) l) (SUB_LIST (r * s, r) l) = l:'a list`
      ASSUME_TAC THENL [
      MATCH_MP_TAC SUB_LIST_SPLIT_EQ THEN ASM_REWRITE_TAC[MULT_SUC] THEN ARITH_TAC;
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `SUB_LIST (0, r * s) l =
       ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) l) s) []:'a list`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `APPEND (SUB_LIST (0,r * s) l) (SUB_LIST (r * s,r) l) = l:'a list` THEN
    UNDISCH_TAC `SUB_LIST (0,r * s) l = ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i,r) l) s) []:'a list` THEN
    SIMP_TAC[APPEND_ITLIST_APPEND_NIL]
  ]);;

(* ========================================================================= *)
(* Helper lemmas: word arithmetic                                            *)
(* ========================================================================= *)

let VAL_WORD_EXACT = prove(
  `!n. n < 2 EXP dimindex(:N) ==> val(word n : N word) = n`,
  REWRITE_TAC[VAL_WORD] THEN SIMP_TAC[MOD_LT]);;

let WORD_PACKED_EQ = prove(
 `!(x:N word) (y:N word).
    dimindex(:N) = l * k /\ 0 < l /\ l <= dimindex(:M)
    ==> (x = y <=>
         !i. i < k
             ==> word_subword x (l*i, l) : (M) word =
                 word_subword y (l*i, l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
   DISCH_TAC THEN
   GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `j:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `j DIV l`) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `j < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `0 < l ==> ~(l = 0)`; MULT_SYM];
    DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\(w:M word). bit (j MOD l) w` th)) THEN
    REWRITE_TAC[BIT_WORD_SUBWORD] THEN
    SUBGOAL_THEN `j MOD l < MIN l (dimindex(:M))`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_SIMP_TAC[ARITH_RULE `l <= m ==> MIN l m = l`;
                   MOD_LT_EQ; ARITH_RULE `0 < l ==> ~(l = 0)`];
     ASM_SIMP_TAC[DIVISION_SIMP; ARITH_RULE `0 < l ==> ~(l = 0)`]]]]);;

let WORD_SUBWORD_NUM_OF_WORDLIST = prove
 (`!(ls:(L word)list) k.
    dimindex(:KL) = dimindex(:L) * LENGTH ls /\
    k < LENGTH ls
    ==> word_subword (word (num_of_wordlist ls) : KL word) (dimindex(:L)*k, dimindex(:L)) : L word = EL k ls`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN n n = n`] THEN
  SUBGOAL_THEN `val (word (num_of_wordlist (ls:(L word)list)) : KL word) = num_of_wordlist ls` SUBST1_TAC THENL
  [W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o lhand o snd) THEN
   ANTS_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (dimindex(:L) * LENGTH (ls:(L word)list))` THEN
    REWRITE_TAC[NUM_OF_WORDLIST_BOUND; LE_EXP; LE_REFL] THEN ASM_ARITH_TAC;
    SIMP_TAC[]];
   MP_TAC(ISPECL [`ls:(L word)list`; `k:num`] NUM_OF_WORDLIST_EL) THEN
   ASM_REWRITE_TAC[]]);;

let NUM_OF_WORDLIST_FLATTEN = prove
 (`!(ll:((N word) list) list) k.
     ALL (\l. LENGTH l = k) ll /\
     dimindex(:N) * k = dimindex(:M)
     ==> num_of_wordlist (ITLIST APPEND ll []) =
         num_of_wordlist (MAP ((word:num->M word) o num_of_wordlist) ll)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MAP; num_of_wordlist; ALL] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; num_of_wordlist; o_THM] THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  IMP_REWRITE_TAC [VAL_WORD_EXACT] THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(h:(N word)list))` THEN
  REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH] THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* ========================================================================= *)
(* Helper lemmas: byte splitting                                             *)
(* ========================================================================= *)

let NUM_BIT_DECOMPOSE_UNIQ = prove(
  `!a b t k. a < 2 EXP k
    ==> (a + 2 EXP k * b = t <=> (a = t MOD 2 EXP k /\ b = t DIV 2 EXP k))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES];
    STRIP_TAC THEN
    MP_TAC (SPECL [`t:num`; `2 EXP k`] DIVISION) THEN
    SIMP_TAC[EXP_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let READ_BYTES_SPLIT_ANY = prove(
  `read (bytes(a : int64,k+l)) s = t <=>
   read (bytes(a,k)) s = t MOD 2 EXP (8*k) /\
   read (bytes(word_add a (word k), l)) s = t DIV 2 EXP (8*k)`,
  let bound = prove(`read (bytes (a : int64,k)) s < 2 EXP (8*k)`,
    REWRITE_TAC[READ_BYTES_BOUND]) in
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[MATCH_MP NUM_BIT_DECOMPOSE_UNIQ bound]);;

(* ========================================================================= *)
(* Helper utilities: word subterm search and binary tree conversion           *)
(* ========================================================================= *)

let is_word_type_n n ty =
  is_type ty &&
  let name, args = dest_type ty in
  name = "word" && length args = 1 &&
  Num.int_of_num (dest_finty (hd args)) = n;;

let rec find_word_subterm_n n tm =
  if is_word_type_n n (type_of tm) then Some tm
  else if is_comb tm then
    match find_word_subterm_n n (rator tm) with
    | Some t -> Some t
    | None -> find_word_subterm_n n (rand tm)
  else if is_abs tm then find_word_subterm_n n (body tm)
  else None;;

let BINOP_CONV_N n cv =
  let rec go depth i tm =
    if depth <= 0 then cv i tm
    else
      let half = 1 lsl (depth - 1) in
      COMB2_CONV (RAND_CONV (go (depth-1) (half + i))) (go (depth-1) i) tm in
  go n 0;;
