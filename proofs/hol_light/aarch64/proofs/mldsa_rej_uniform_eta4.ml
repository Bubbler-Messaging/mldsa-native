(*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* Rejection sampling with eta=4 for ML-DSA AArch64.                        *)
(*                                                                           *)
(* Filters 4-bit nibbles < 9, maps accepted values n to (4 - n) as int32.   *)
(* Uses a 256-entry lookup table indexed by 8-bit masks (16 bytes each).     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "aarch64/proofs/aarch64_utils.ml";;
needs "aarch64/proofs/mldsa_rej_uniform_eta_table.ml";;

(**** print_literal_from_elf "aarch64/mldsa/mldsa_rej_uniform_eta4.o";;
 ****)

let mldsa_rej_uniform_eta4_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta4_mc" "aarch64/mldsa/mldsa_rej_uniform_eta4.o"
(*** BYTECODE START ***)
[
  0xd10903ff;       (* arm_SUB SP SP (rvalue (word 576)) *)
  0xd2800027;       (* arm_MOV X7 (rvalue (word 1)) *)
  0xf2a00047;       (* arm_MOVK X7 (word 2) 16 *)
  0xf2c00087;       (* arm_MOVK X7 (word 4) 32 *)
  0xf2e00107;       (* arm_MOVK X7 (word 8) 48 *)
  0x4e081cff;       (* arm_INS_GEN Q31 X7 0 64 *)
  0xd2800207;       (* arm_MOV X7 (rvalue (word 16)) *)
  0xf2a00407;       (* arm_MOVK X7 (word 32) 16 *)
  0xf2c00807;       (* arm_MOVK X7 (word 64) 32 *)
  0xf2e01007;       (* arm_MOVK X7 (word 128) 48 *)
  0x4e181cff;       (* arm_INS_GEN Q31 X7 64 64 *)
  0x4f00853e;       (* arm_MOVI Q30 (word 2533313445691401) *)
  0x4f008487;       (* arm_MOVI Q7 (word 1125917086973956) *)
  0x910003e8;       (* arm_ADD X8 SP (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0x6e301e10;       (* arm_EOR_VEC Q16 Q16 Q16 128 *)
  0x3c8404f0;       (* arm_STR Q16 X7 (Postimmediate_Offset (word 64)) *)
  0x3c9d00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f00f0;       (* arm_STR Q16 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100816b;       (* arm_ADD X11 X11 (rvalue (word 32)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54ffff4b;       (* arm_BLT (word 2097128) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xd2800009;       (* arm_MOV X9 (rvalue (word 0)) *)
  0xd2802004;       (* arm_MOV X4 (rvalue (word 256)) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x54000482;       (* arm_BCS (word 144) *)
  0xd1002042;       (* arm_SUB X2 X2 (rvalue (word 8)) *)
  0x0cdf7020;       (* arm_LDR D0 X1 (Postimmediate_Offset (word 8)) *)
  0x0f00e5fa;       (* arm_MOVI Q26 (word 1085102592571150095) *)
  0x0e3a1c1b;       (* arm_AND_VEC Q27 Q0 Q26 64 *)
  0x2f0c041c;       (* arm_USHR_VEC Q28 Q0 4 8 64 *)
  0x0e1c3b7a;       (* arm_ZIP1 Q26 Q27 Q28 8 64 *)
  0x0e1c7b7d;       (* arm_ZIP2 Q29 Q27 Q28 8 64 *)
  0x2f08a750;       (* arm_USHLL_VEC Q16 Q26 0 8 *)
  0x2f08a7b1;       (* arm_USHLL_VEC Q17 Q29 0 8 *)
  0x6e7037c4;       (* arm_CMHI_VEC Q4 Q30 Q16 16 128 *)
  0x6e7137c5;       (* arm_CMHI_VEC Q5 Q30 Q17 16 128 *)
  0x4e3f1c84;       (* arm_AND_VEC Q4 Q4 Q31 128 *)
  0x4e3f1ca5;       (* arm_AND_VEC Q5 Q5 Q31 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x3cec7878;       (* arm_LDR Q24 X3 (Shiftreg_Offset X12 4) *)
  0x3ced7879;       (* arm_LDR Q25 X3 (Shiftreg_Offset X13 4) *)
  0x4e205884;       (* arm_CNT Q4 Q4 128 *)
  0x4e2058a5;       (* arm_CNT Q5 Q5 128 *)
  0x6e703894;       (* arm_UADDLV Q20 Q4 8 16 *)
  0x6e7038b5;       (* arm_UADDLV Q21 Q5 8 16 *)
  0x1e26028c;       (* arm_FMOV_FtoI W12 Q20 0 32 *)
  0x1e2602ad;       (* arm_FMOV_FtoI W13 Q21 0 32 *)
  0x4e180210;       (* arm_TBL Q16 [Q16] Q24 128 *)
  0x4e190231;       (* arm_TBL Q17 [Q17] Q25 128 *)
  0x4c0074f0;       (* arm_STR Q16 X7 No_Offset *)
  0x8b0c04e7;       (* arm_ADD X7 X7 (Shiftedreg X12 LSL 1) *)
  0x4c0074f1;       (* arm_STR Q17 X7 No_Offset *)
  0x8b0d04e7;       (* arm_ADD X7 X7 (Shiftedreg X13 LSL 1) *)
  0x8b0d018c;       (* arm_ADD X12 X12 X13 *)
  0x8b0c0129;       (* arm_ADD X9 X9 X12 *)
  0xf100205f;       (* arm_CMP X2 (rvalue (word 8)) *)
  0x54fffb82;       (* arm_BCS (word 2097008) *)
  0xeb04013f;       (* arm_CMP X9 X4 *)
  0x9a843129;       (* arm_CSEL X9 X9 X4 Condition_CC *)
  0xd280000b;       (* arm_MOV X11 (rvalue (word 0)) *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0x3cc204f0;       (* arm_LDR Q16 X7 (Postimmediate_Offset (word 32)) *)
  0x3cdf00f2;       (* arm_LDR Q18 X7 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e7084f0;       (* arm_SUB_VEC Q16 Q7 Q16 16 128 *)
  0x6e7284f2;       (* arm_SUB_VEC Q18 Q7 Q18 16 128 *)
  0x4f10a611;       (* arm_SSHLL2_VEC Q17 Q16 0 16 *)
  0x0f10a610;       (* arm_SSHLL_VEC Q16 Q16 0 16 *)
  0x4f10a653;       (* arm_SSHLL2_VEC Q19 Q18 0 16 *)
  0x0f10a652;       (* arm_SSHLL_VEC Q18 Q18 0 16 *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9d0011;       (* arm_STR Q17 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0012;       (* arm_STR Q18 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f0013;       (* arm_STR Q19 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x9100416b;       (* arm_ADD X11 X11 (rvalue (word 16)) *)
  0xf104017f;       (* arm_CMP X11 (rvalue (word 256)) *)
  0x54fffe4b;       (* arm_BLT (word 2097096) *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x910903ff;       (* arm_ADD SP SP (rvalue (word 576)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_REJ_UNIFORM_ETA4_EXEC = ARM_MK_EXEC_RULE mldsa_rej_uniform_eta4_mc;;

let LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC =
  REWRITE_CONV[mldsa_rej_uniform_eta4_mc] `LENGTH mldsa_rej_uniform_eta4_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

(* Nibble extraction *)
let NIBBLE_PAIR = define
  `NIBBLE_PAIR (b:byte) =
   [word(val b MOD 16):int16; word(val b DIV 16):int16]`;;

let NIBBLES_OF_BYTES = define
  `NIBBLES_OF_BYTES [] = ([]:(int16)list) /\
   NIBBLES_OF_BYTES (CONS (b:byte) t) =
   APPEND (NIBBLE_PAIR b) (NIBBLES_OF_BYTES t)`;;

let NIBBLES_OF_BYTES_APPEND = prove
 (`!l1 l2. NIBBLES_OF_BYTES(APPEND l1 l2) =
           APPEND (NIBBLES_OF_BYTES l1) (NIBBLES_OF_BYTES l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; APPEND; APPEND_ASSOC]);;

(* Rejection sampling spec *)
let REJ_NIBBLES_ETA4 = define
  `REJ_NIBBLES_ETA4 l =
   FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES l)`;;

let REJ_SAMPLE_ETA4 = define
  `REJ_SAMPLE_ETA4 l =
   MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
       (REJ_NIBBLES_ETA4 l)`;;

let REJ_NIBBLES_ETA4_EMPTY = prove
 (`REJ_NIBBLES_ETA4 [] = []`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; FILTER]);;

let REJ_SAMPLE_ETA4_EMPTY = prove
 (`REJ_SAMPLE_ETA4 [] = []`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; REJ_NIBBLES_ETA4_EMPTY; MAP]);;

let REJ_NIBBLES_ETA4_APPEND = prove
 (`!l1 l2. REJ_NIBBLES_ETA4(APPEND l1 l2) =
           APPEND (REJ_NIBBLES_ETA4 l1) (REJ_NIBBLES_ETA4 l2)`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_APPEND; FILTER_APPEND]);;

let REJ_SAMPLE_ETA4_APPEND = prove
 (`!l1 l2. REJ_SAMPLE_ETA4(APPEND l1 l2) =
           APPEND (REJ_SAMPLE_ETA4 l1) (REJ_SAMPLE_ETA4 l2)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4; REJ_NIBBLES_ETA4_APPEND; MAP_APPEND]);;

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC);;

let LENGTH_REJ_NIBBLES_ETA4 = prove
 (`!l:byte list. LENGTH(REJ_NIBBLES_ETA4 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES_OF_BYTES l:int16 list)` THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_FILTER]; ALL_TAC] THEN
  SPEC_TAC(`l:byte list`,`l:byte list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND; LE_0] THEN
  UNDISCH_TAC `LENGTH(NIBBLES_OF_BYTES t:int16 list) <=
               2 * LENGTH(t:byte list)` THEN ARITH_TAC);;

(* Helper lemma *)
let EIGHT_N_LE_BUFLEN = prove
 (`(!m. m < N ==> ~(buflen < 8 * (m + 1))) /\ 0 < N
   ==> 8 * N <= buflen`,
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `N - 1 < N <=> 0 < N`] THEN ARITH_TAC);;

(* Q31 word_insert simplification *)
let WORD_INSERT_Q31 = prove(
  `word_insert ((word_insert:int128->num#num->int64->int128) q (0,64)
    (word 2251816993685505)) (64,64) (word 36029071898968080:int64) =
    (word 664619068533544770747334646890102785:int128)`,
  CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* Additional helpers (from rej_uniform proof pattern)                       *)
(* ========================================================================= *)

let DIMINDEX_16 = DIMINDEX_CONV `dimindex(:16)`;;

(* Nibble expansion for 8 bytes *)
let NIBBLES_OF_BYTES_8 = prove(
  `!b0 b1 b2 b3 b4 b5 b6 b7:byte.
    NIBBLES_OF_BYTES [b0;b1;b2;b3;b4;b5;b6;b7] =
    APPEND [word(val b0 MOD 16); word(val b0 DIV 16);
            word(val b1 MOD 16); word(val b1 DIV 16);
            word(val b2 MOD 16); word(val b2 DIV 16);
            word(val b3 MOD 16); word(val b3 DIV 16)]
           [word(val b4 MOD 16); word(val b4 DIV 16);
            word(val b5 MOD 16); word(val b5 DIV 16);
            word(val b6 MOD 16); word(val b6 DIV 16);
            word(val b7 MOD 16); word(val b7 DIV 16):int16]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN REWRITE_TAC[APPEND]);;

(* REJ_NIBBLES_ETA4 splits into two groups of 8 nibbles *)
let REJ_NIBBLES_ETA4_8 = prove(
  `!b0 b1 b2 b3 b4 b5 b6 b7:byte.
    REJ_NIBBLES_ETA4 [b0;b1;b2;b3;b4;b5;b6;b7] =
    APPEND
      (FILTER (\x:int16. val x < 9)
        [word(val b0 MOD 16); word(val b0 DIV 16);
         word(val b1 MOD 16); word(val b1 DIV 16);
         word(val b2 MOD 16); word(val b2 DIV 16);
         word(val b3 MOD 16); word(val b3 DIV 16)])
      (FILTER (\x:int16. val x < 9)
        [word(val b4 MOD 16); word(val b4 DIV 16);
         word(val b5 MOD 16); word(val b5 DIV 16);
         word(val b6 MOD 16); word(val b6 DIV 16);
         word(val b7 MOD 16); word(val b7 DIV 16)])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_8; FILTER_APPEND]);;

(* Length of nibbles from 8 bytes *)
let LENGTH_NIBBLES_OF_BYTES = prove(
  `!l:byte list. LENGTH(NIBBLES_OF_BYTES l) = 2 * LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND] THEN
  ARITH_TAC);;

let BYTES_EQ_NUM_OF_WORDLIST_APPEND = prove
 (`!m (a:int64) (s:S) lis1 (lis2:(N word)list) len1 len2.
        dimindex(:N) * LENGTH lis1 = 8 * len1
        ==>  (read (m :> bytes(a,len1+len2)) s =
              num_of_wordlist(APPEND lis1 lis2) <=>
              read (m :> bytes(a,len1)) s = num_of_wordlist lis1 /\
              read (m :> bytes(word_add a (word len1),len2)) s =
              num_of_wordlist lis2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN ASM_REWRITE_TAC[LE_REFL]);;

(* Merge 2 x bytes64 reads into bytes128 reads *)
let MEMORY_128_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 16*i) in
      READ_MEMORY_MERGE_CONV 1 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* ========================================================================= *)
(* Main correctness theorem                                                  *)
(* ========================================================================= *)

let MLDSA_REJ_UNIFORM_ETA4_CORRECT = prove
 (`!res buf buflen table (inlist:byte list) pc stackpointer.
        8 divides val buflen /\
        8 <= val buflen /\
        LENGTH inlist = val buflen /\
        ALL (nonoverlapping (stackpointer,576))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (buf,val buflen); (table,4096)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (stackpointer,576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                  read PC s = word(pc + 4) /\
                  read SP s = stackpointer /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mldsa_rej_uniform_eta_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = word(pc + 336) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4 inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(stackpointer,576)])`,

  (* === INTRO: unpack preconditions, keep nonoverlapping in word form === *)
  REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC;
              fst MLDSA_REJ_UNIFORM_ETA4_EXEC;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              C_ARGUMENTS; ALL; C_RETURN] THEN
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:byte list`; `pc:num`; `stackpointer:int64`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (* === Split: computation (pc+4 to pc+0x100) and writeback (to pc+0x150) *)
  ENSURES_SEQUENCE_TAC `pc + 0x100`
   `\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
        read PC s = word(pc + 0x100) /\
        read X0 s = res /\
        read X4 s = word 256 /\
        read X8 s = stackpointer /\
        read Q7 s = word 20769504351625144638033088116686852 /\
        ALL (nonoverlapping (res,1024))
            [(word pc,344); (stackpointer,576)] /\
        ?n. let niblist = REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * n) inlist) in
            let niblen = LENGTH niblist in
            niblen < 272 /\
            read X9 s = word niblen /\
            (buflen < 8 * (n + 1) \/ 256 <= niblen) /\
            read (memory :> bytes (stackpointer,2 * niblen)) s =
            num_of_wordlist niblist` THEN
  CONJ_TAC THENL
   [ALL_TAC; (* writeback phase deferred to second conjunct *)

    (* ============================================================= *)
    (* WRITEBACK PHASE: from pc+0x100 to pc+0x150                    *)
    (* CMP+CSEL to cap at 256, then 16-iteration copy loop with      *)
    (* (4 - nibble) transform and sign extension to 32-bit.          *)
    (* ============================================================= *)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ABBREV_TAC `niblist = REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * n) inlist)` THEN
    ABBREV_TAC `niblen = LENGTH(niblist:int16 list)` THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    VAL_INT64_TAC `niblen:num` THEN
    BIGNUM_LDIGITIZE_TAC "b_"
      `read (memory :> bytes(stackpointer,8 * 64)) s0` THEN
    MEMORY_128_FROM_64_TAC "stackpointer" 0 32 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--245) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    (*** Postcondition: output = REJ_SAMPLE_ETA4(inlist) truncated to 256 ***)
    (*** The writeback loop reads halfwords from stack, computes (4-n), ***)
    (*** sign-extends to 32-bit, and stores to output. This matches     ***)
    (*** REJ_SAMPLE_ETA4 = MAP (\x. word_sx(word_sub(word 4) x)) o     ***)
    (*** REJ_NIBBLES_ETA4. The proof connects output to spec via the    ***)
    (*** stack data and READ_BYTES_MOD for truncation.                  ***)
    (*** Pattern: rej_uniform lines 559-615.                            ***)
    (*** Try: see if SUBGOAL_THEN + DISJ_CASES_TAC resolves it ***)
    SUBGOAL_THEN
     `read (memory :> bytes (res,4 * MIN 256 niblen)) s245 =
      num_of_wordlist (SUB_LIST (0,256) (REJ_SAMPLE_ETA4
        (SUB_LIST(0,8 * n) inlist)):int32 list)`
    ASSUME_TAC THENL
     [REWRITE_TAC[REJ_SAMPLE_ETA4; NUM_OF_WORDLIST_SUB_LIST_0;
                  DIMINDEX_32; LENGTH_MAP] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[ARITH_RULE `4 * MIN 256 l = MIN (4 * l) 1024`] THEN
      REWRITE_TAC[ARITH_RULE `32 * 256 = 8 * 1024`] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `MIN a b = MIN b a`] THEN
      REWRITE_TAC[GSYM READ_BYTES_MOD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      REWRITE_TAC[ARITH_RULE `1024 = 8 * 128`] THEN
      CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(READ_MEMORY_SPLIT_CONV 1))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [(*** Case 1: buflen < 8*(n+1) — input exhausted ***)
      SUBGOAL_THEN `SUB_LIST (0,8 * n) (inlist:byte list) = inlist`
      SUBST_ALL_TAC THENL
       [MATCH_MP_TAC SUB_LIST_REFL THEN
        UNDISCH_TAC `buflen < 8 * (n + 1)` THEN
        UNDISCH_TAC `LENGTH inlist = buflen` THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
        SIMP_TAC[LEFT_IMP_EXISTS_THM; LE_MULT_LCANCEL; LT_MULT_LCANCEL] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0]] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM COND_RAND] THEN
      REWRITE_TAC[ARITH_RULE `(if l < p then l else p) = MIN p l`];
      (*** Case 2: 256 <= niblen — enough samples ***)
      ASM_REWRITE_TAC[GSYM NOT_LE; LENGTH_SUB_LIST; SUB_0] THEN
      MATCH_MP_TAC(MESON[]
       `y = x /\ (y = x ==> P) ==> word x = word y /\ P`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
        REWRITE_TAC[REJ_SAMPLE_ETA4; LENGTH_MAP] THEN
        TRANS_TAC LE_TRANS `niblen:num` THEN ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(SYM(ASSUME `LENGTH(niblist:int16 list) = niblen`)) THEN
        EXPAND_TAC "niblist" THEN
        MP_TAC(ISPECL [`inlist:byte list`; `8 * n`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SYM th]) THEN
        REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND; LE_ADD];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN
       `SUB_LIST (0,256) (REJ_SAMPLE_ETA4 inlist) =
        SUB_LIST (0,256) (REJ_SAMPLE_ETA4 (SUB_LIST(0,8*n) inlist))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`inlist:byte list`; `8 * n`]
          SUB_LIST_TOPSPLIT) THEN
        DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
        ASM_SIMP_TAC[REJ_SAMPLE_ETA4_APPEND; SUB_LIST_APPEND_LEFT] THEN
        REWRITE_TAC[REJ_SAMPLE_ETA4; LENGTH_MAP] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
       `256 <= l ==> 4 * 256 = 4 * MIN 256 l`)) THEN
      FIRST_ASSUM ACCEPT_TAC]] THEN

  (* ================================================================= *)
  (* COMPUTATION PHASE: from pc+4 to pc+0x100                          *)
  (* Preamble (setup + stack zeroing) + main loop + post-loop CMP      *)
  (* ================================================================= *)

  (* --- WOP characterization of loop iteration count N --- *)
  SUBGOAL_THEN
   `?i. buflen < 8 * (i + 1) \/
        256 <= LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN

  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LE] THEN STRIP_TAC THEN

  (* --- 0 < N follows from 8 <= buflen --- *)
  SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 < N <=> ~(N = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES;
                SUB_LIST_CLAUSES; REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN
    UNDISCH_TAC `8 <= buflen` THEN ARITH_TAC;
    ALL_TAC] THEN

  (* --- Set up loop: ENSURES_WHILE_UP_TAC --- *)
  ENSURES_WHILE_UP_TAC `N:num` `pc + 0x6c` `pc + 0xf8`
   `\i s. read (memory :> bytes (table,4096)) s =
          num_of_wordlist mldsa_rej_uniform_eta_table /\
          read (memory :> bytes (buf,buflen)) s = num_of_wordlist inlist /\
          aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
          read Q7 s = word 20769504351625144638033088116686852 /\
          read Q30 s = word 46731384791156575435574448262545417 /\
          read Q31 s = word 664619068533544770747334646890102785 /\
          let niblist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist) in
          let niblen = LENGTH niblist in
          read X0 s = res /\
          read X1 s = word_add buf (word(8 * i)) /\
          read X2 s = word_sub (word buflen) (word(8 * i)) /\
          read X3 s = table /\
          read X4 s = word 256 /\
          read X7 s = word_add stackpointer (word(2 * niblen)) /\
          read X8 s = stackpointer /\
          read X9 s = word niblen /\
          read (memory :> bytes (stackpointer,2 * niblen)) s =
          num_of_wordlist niblist` THEN
  REPEAT CONJ_TAC THENL
   [(*** Subgoal 1: 0 < N ***)
    ASM_ARITH_TAC;

    (*** Subgoal 2: Pre-loop initialization — 75 ARM steps ***)
    (*** From pc+4 to pc+0x6c: setup V30/V31/V7, zero stack, init regs ***)
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `q31_init:int128` `read Q31` THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--75) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_INSERT_Q31]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES;
                REJ_NIBBLES_ETA4_EMPTY] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[LENGTH] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; WORD_SUB_0] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist];

    (*** Subgoal 3: Loop body — 35 ARM steps + functional correctness ***)
    (*** From pc+0x6c (invariant i) to pc+0xf8 (invariant i+1) ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC `curlist = REJ_NIBBLES_ETA4(SUB_LIST(0,8 * i) inlist)` THEN
    ABBREV_TAC `curlen = LENGTH(curlist:int16 list)` THEN
    CONV_TAC(RATOR_CONV(LAND_CONV(TOP_DEPTH_CONV let_CONV))) THEN
    ASM_REWRITE_TAC[] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i:num < N`)) THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_LE; NOT_LT] THEN
    STRIP_TAC THEN
    (*** Steps 1-2: CMP X9,X4 + BCS ***)
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN

    (*** Resolve BCS conditional PC: curlen < 256 so BCS not taken ***)
    SUBGOAL_THEN `~(256 <= val(word curlen:int64))` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      UNDISCH_TAC `curlen < 256` THEN UNDISCH_TAC `buflen < 2 EXP 64` THEN
      UNDISCH_TAC `LENGTH(curlist:int16 list) = curlen` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(256 <= val(word curlen:int64))`]) THEN

    (*** Steps 3-35: remaining loop body ***)
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (3--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (*** Subgoal 4: Back edge — 2 ARM steps from pc+0xf8 to pc+0x6c ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `8 <= val(word_sub (word buflen:int64) (word (8 * i)))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
      VAL_INT64_TAC `8 * i` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(buflen < 8 * (i + 1))` THEN ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[VAL_WORD_SUB_CASES; VAL_WORD_LE;
                 ARITH_RULE `8 <= x ==> 8 <= x`];

    (*** Subgoal 5: Post-loop exit — from pc+0xf8 to pc+0x100 ***)
    (*** Handle both cases: input exhausted or niblen >= 256 ***)

    (*** First prove niblen < 272 ***)
    SUBGOAL_THEN
     `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * N) inlist)) < 272`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `N = 0` THENL
       [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES;
                        REJ_NIBBLES_ETA4_EMPTY] THEN
        REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
        FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`)] THEN
      ASM_REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
      MATCH_MP_TAC(ARITH_RULE
       `l' <= l + 16 ==> ~(b < x) /\ l < 256 ==> l' < 272`) THEN
      MP_TAC(ISPECL [`inlist:byte list`; `8 * (N - 1)`; `8`; `0`]
          SUB_LIST_SPLIT) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(N = 0) ==> 8 * (N - 1) + 8 = 8 * N`] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND] THEN
      REWRITE_TAC[LENGTH_APPEND; LE_ADD_LCANCEL; ADD_CLAUSES] THEN
      TRANS_TAC LE_TRANS
       `2 * LENGTH(SUB_LIST(8 * (N-1),8) (inlist:byte list))` THEN
      CONJ_TAC THENL [REWRITE_TAC[LENGTH_REJ_NIBBLES_ETA4]; ALL_TAC] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC;
      ALL_TAC] THEN
    VAL_INT64_TAC
     `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,8 * N) inlist))` THEN

    (*** Establish val of word_sub for back edge check ***)
    SUBGOAL_THEN
     `8 <= val(word_sub (word buflen:int64) (word (8 * N))) <=>
      8 * (N + 1) <= buflen`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `8 * N < 2 EXP 64` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
        MAP_EVERY VAL_INT64_TAC [`8 * N`; `buflen:num`]] THEN
      ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN

    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_CASES_TAC `8 * (N + 1) <= buflen` THENL
     [(*** Case B: more input available, back edge taken,
           then early exit at loop head because niblen >= 256 ***)
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (3--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `N:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `8 * N = 8 * N`];

      (*** Case A: input exhausted, back edge not taken ***)
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
          (REWRITE_RULE[CONJ_ASSOC] ENSURES_TRANS_SIMPLE))) THEN
      CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]]]);;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA4_MC] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ------------------------------------------------------------------------- *)
(* Subroutine form: includes stack frame allocation/deallocation and return.  *)
(* C signature: uint64_t mld_rej_uniform_eta4_asm(int32_t *r,                *)
(*   const uint8_t *buf, unsigned buflen, const uint8_t *table);             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT = prove
 (`!res buf buflen table (inlist:byte list) pc stackpointer returnaddress.
        8 divides val buflen /\
        8 <= val buflen /\
        LENGTH inlist = val buflen /\
        ALL (nonoverlapping (word_sub stackpointer (word 576),576))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (buf,val buflen); (table,4096)] /\
        ALL (nonoverlapping (res,1024))
            [(word pc,LENGTH mldsa_rej_uniform_eta4_mc);
             (word_sub stackpointer (word 576),576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [res;buf;buflen;table] s /\
                  read(memory :> bytes(table,4096)) s =
                  num_of_wordlist mldsa_rej_uniform_eta_table /\
                  read(memory :> bytes(buf,val buflen)) s =
                  num_of_wordlist inlist)
             (\s. read PC s = returnaddress /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4 inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                  num_of_wordlist outlist)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024);
                         memory :> bytes(word_sub stackpointer (word 576),576)])`,
  REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(1,2)
   MLDSA_REJ_UNIFORM_ETA4_EXEC
   (REWRITE_RULE[fst MLDSA_REJ_UNIFORM_ETA4_EXEC]
     (CONV_RULE LENGTH_SIMPLIFY_CONV MLDSA_REJ_UNIFORM_ETA4_CORRECT))
   `[]` 0);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "aarch64/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_rej_uniform_eta4" subroutine_signatures)
    MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT
    MLDSA_REJ_UNIFORM_ETA4_EXEC;;

let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e res buf buflen table pc stackpointer returnaddress.
           ALL (nonoverlapping (word_sub stackpointer (word 576),576))
           [word pc,LENGTH mldsa_rej_uniform_eta4_mc;
            buf,val buflen; table,4096] /\
           ALL (nonoverlapping (res,1024))
           [word pc,LENGTH mldsa_rej_uniform_eta4_mc;
            word_sub stackpointer (word 576),576]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [res; buf; buflen; table] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events res buf buflen table pc
                        (word_sub stackpointer (word 576))
                        returnaddress /\
                        memaccess_inbounds e2
                        [buf,val buflen; table,4096;
                         word_sub stackpointer (word 576),576]
                        [res,1024;
                         word_sub stackpointer (word 576),576])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars
   MLDSA_REJ_UNIFORM_ETA4_EXEC);;
