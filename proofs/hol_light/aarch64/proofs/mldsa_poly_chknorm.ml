(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness of poly_chknorm:                                   *)
(* Check if any polynomial coefficient has absolute value >= bound           *)
(* Returns 1 if norm check fails (|coeff| >= bound), 0 otherwise             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "aarch64/proofs/aarch64_utils.ml";;

(**** print_literal_from_elf "aarch64/mldsa/mldsa_poly_chknorm.o";;
 ****)

let mldsa_poly_chknorm_mc = define_assert_from_elf "mldsa_poly_chknorm_mc" "aarch64/mldsa/mldsa_poly_chknorm.o"
(*** BYTECODE START ***)
[
  0x4e040c34;       (* arm_DUP_GEN Q20 X1 32 128 *)
  0x6e351eb5;       (* arm_EOR_VEC Q21 Q21 Q21 128 *)
  0xd2800202;       (* arm_MOV X2 (rvalue (word 16)) *)
  0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3dc00802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3dc00c03;       (* arm_LDR Q3 X0 (Immediate_Offset (word 48)) *)
  0x3cc40400;       (* arm_LDR Q0 X0 (Postimmediate_Offset (word 64)) *)
  0x4ea0b821;       (* arm_ABS_VEC Q1 Q1 32 128 *)
  0x4eb43c21;       (* arm_CMGE_VEC Q1 Q1 Q20 32 128 *)
  0x4ea11eb5;       (* arm_ORR_VEC Q21 Q21 Q1 128 *)
  0x4ea0b842;       (* arm_ABS_VEC Q2 Q2 32 128 *)
  0x4eb43c42;       (* arm_CMGE_VEC Q2 Q2 Q20 32 128 *)
  0x4ea21eb5;       (* arm_ORR_VEC Q21 Q21 Q2 128 *)
  0x4ea0b863;       (* arm_ABS_VEC Q3 Q3 32 128 *)
  0x4eb43c63;       (* arm_CMGE_VEC Q3 Q3 Q20 32 128 *)
  0x4ea31eb5;       (* arm_ORR_VEC Q21 Q21 Q3 128 *)
  0x4ea0b800;       (* arm_ABS_VEC Q0 Q0 32 128 *)
  0x4eb43c00;       (* arm_CMGE_VEC Q0 Q0 Q20 32 128 *)
  0x4ea01eb5;       (* arm_ORR_VEC Q21 Q21 Q0 128 *)
  0xf1000442;       (* arm_SUBS X2 X2 (rvalue (word 1)) *)
  0x54fffde1;       (* arm_BNE (word 2097084) *)
  0x6eb0aab5;       (* arm_UMAXV Q21 Q21 4 32 *)
  0x1e2602a0;       (* arm_FMOV_FtoI W0 Q21 0 32 *)
  0x12000000;       (* arm_AND W0 W0 (rvalue (word 1)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_POLY_CHKNORM_EXEC = ARM_MK_EXEC_RULE mldsa_poly_chknorm_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_POLY_CHKNORM_MC =
  REWRITE_CONV[mldsa_poly_chknorm_mc] `LENGTH mldsa_poly_chknorm_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLDSA_POLY_CHKNORM_PREAMBLE_LENGTH = new_definition
  `MLDSA_POLY_CHKNORM_PREAMBLE_LENGTH = 0`;;

let MLDSA_POLY_CHKNORM_POSTAMBLE_LENGTH = new_definition
  `MLDSA_POLY_CHKNORM_POSTAMBLE_LENGTH = 4`;;

let MLDSA_POLY_CHKNORM_CORE_START = new_definition
  `MLDSA_POLY_CHKNORM_CORE_START = MLDSA_POLY_CHKNORM_PREAMBLE_LENGTH`;;

let MLDSA_POLY_CHKNORM_CORE_END = new_definition
  `MLDSA_POLY_CHKNORM_CORE_END = LENGTH mldsa_poly_chknorm_mc - MLDSA_POLY_CHKNORM_POSTAMBLE_LENGTH`;;

let CHKNORM_LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_POLY_CHKNORM_MC;
              MLDSA_POLY_CHKNORM_CORE_START; MLDSA_POLY_CHKNORM_CORE_END;
              MLDSA_POLY_CHKNORM_PREAMBLE_LENGTH; MLDSA_POLY_CHKNORM_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Helper lemmas                                                             *)
(* ------------------------------------------------------------------------- *)

(* ival(iword(abs x)) = abs x when abs x < 2^31 *)
let IVAL_IWORD_ABS_32 = prove(
  `!x:int. abs x < &2 pow 31 ==> ival(iword (abs x) : 32 word) = abs x`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPEC `x:int` INT_ABS_POS) THEN ASM_INT_ARITH_TAC);;

(* MAX of {0, 0xFFFFFFFF} conditionals collapses to a single conditional *)
let MAX_COND_4_LEMMA = prove(
  `MAX (if b0 then 4294967295 else 0)
       (MAX (if b1 then 4294967295 else 0)
            (MAX (if b2 then 4294967295 else 0)
                 (if b3 then 4294967295 else 0))) =
   if (b0 \/ b1 \/ b2 \/ b3) then 4294967295 else 0`,
  MAP_EVERY BOOL_CASES_TAC [`b0:bool`; `b1:bool`; `b2:bool`; `b3:bool`] THEN
  REWRITE_TAC[] THEN ARITH_TAC);;

(* (?i. i < 256 /\ P i) <=> P 0 \/ ... \/ P 255 *)
let EXISTS_LT_256 =
  let p = `P:num->bool` and i_var = `i:num` in
  let mk_p k = mk_comb(p, mk_small_numeral k) in
  let rhs = end_itlist (fun a b -> mk_disj(a,b)) (map mk_p (0--255)) in
  let lhs = mk_exists(i_var,
    mk_conj(mk_comb(mk_comb(`(<)`, i_var), `256`), mk_comb(p, i_var))) in
  let arith_rules =
    ARITH_RULE `i < 1 <=> i = 0` ::
    map (fun k -> ARITH_RULE(subst [mk_small_numeral k, `n:num`;
                                     mk_small_numeral(k-1), `m:num`]
                                    `i < n <=> i = m \/ i < m`)) (2--256) in
  prove(mk_forall(p, mk_eq(lhs, rhs)),
    GEN_TAC THEN REWRITE_TAC arith_rules THEN
    REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[DISJ_ACI]);;

(* word_or of word_neg(word(bitval ...)) combines disjunctively *)
let WORD_OR_NEG_BITVAL = prove(
  `word_or (word_neg (word (bitval b1) : 32 word))
           (word_neg (word (bitval b2) : 32 word)) : 32 word =
   word_neg (word (bitval (b1 \/ b2)))`,
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN
  REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV);;

(* val(word_neg(word(bitval b))) = if b then 0xFFFFFFFF else 0 *)
let VAL_WORD_NEG_BITVAL = prove(
  `val (word_neg (word (bitval b) : 32 word)) = if b then 4294967295 else 0`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_CHKNORM_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc.
        nonoverlapping (word pc, LENGTH mldsa_poly_chknorm_mc) (a, 1024)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_poly_chknorm_mc /\
                  read PC s = word(pc + MLDSA_POLY_CHKNORM_CORE_START) /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read PC s = word(pc + MLDSA_POLY_CHKNORM_CORE_END) /\
                  read X0 s = word(bitval(?i. i < 256 /\ abs(ival(x i)) >= ival bound)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CONV_TAC CHKNORM_LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int32`; `bound:int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; EXISTS_LT_256] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* Expand bounded foralls in precondition to 256 explicit cases *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* Merge bytes32 reads into bytes128 reads (64 merges for 256 coefficients) *)
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 2
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--63))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN
  (* Symbolically execute all instructions until target PC *)
  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLDSA_POLY_CHKNORM_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUBWORD_OR])) 1 THEN
  (* Collapse nested word_or of word_neg pairs, then take val *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_OR_NEG_BITVAL; VAL_WORD_NEG_BITVAL]) THEN
  (* Close the state relation *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* Prove ival(iword(abs(ival x i))) = abs(ival(x i)) for all 256 coefficients *)
  SUBGOAL_THEN
    `!i. i < 256 ==> ival(iword(abs(ival((x:num->int32) i))) : 32 word) = abs(ival(x i))`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD_ABS_32 THEN
   UNDISCH_TAC `(i:num) < 256` THEN SPEC_TAC(`i:num`, `i:num`) THEN
   CONV_TAC EXPAND_CASES_CONV THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Apply the ival/iword simplification for all 256 coefficients *)
  FIRST_X_ASSUM(fun th -> REWRITE_TAC
    (map (fun k -> MATCH_MP th
       (ARITH_RULE(subst [mk_small_numeral k, `n:num`] `n < 256`)))
     (0--255))) THEN
  (* Simplify word_zx round-trip for bound *)
  REWRITE_TAC[prove(
    `ival(word_zx ((word_zx:32 word->64 word) (bound:32 word)) : 32 word) = ival bound`,
    BITBLAST_TAC)] THEN
  (* Rewrite MAX of conditionals to a single conditional *)
  REWRITE_TAC[MAX_COND_4_LEMMA] THEN
  (* Normalize the disjunction order *)
  REWRITE_TAC[DISJ_ACI] THEN
  (* Case split on the condition and simplify word operations *)
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness theorem (includes return)                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_POLY_CHKNORM_SUBROUTINE_CORRECT = prove(
 `!a (x:num->int32) (bound:int32) pc returnaddress.
        nonoverlapping (word pc, LENGTH mldsa_poly_chknorm_mc) (a, 1024)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_poly_chknorm_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; word_zx bound] s /\
                  (!i. i < 256 ==>
                     read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
                  (!i. i < 256 ==> abs(ival(x i)) < &2 pow 31))
             (\s. read PC s = returnaddress /\
                  read X0 s = word(bitval(?i. i < 256 /\ abs(ival(x i)) >= ival bound)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  CONV_TAC CHKNORM_LENGTH_SIMPLIFY_CONV THEN
  let TWEAK_CONV =
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0; EXISTS_LT_256] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_POLY_CHKNORM_EXEC
   (CONV_RULE TWEAK_CONV
     (CONV_RULE CHKNORM_LENGTH_SIMPLIFY_CONV MLDSA_POLY_CHKNORM_CORRECT)));;

