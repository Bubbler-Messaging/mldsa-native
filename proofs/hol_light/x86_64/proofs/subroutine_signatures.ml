(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA x86_64 subroutine signatures for constant-time proofs.            *)
(* Trimmed version of s2n-bignum's x86/proofs/subroutine_signatures.ml.     *)
(* ========================================================================= *)

let subroutine_signatures = [
("keccak_f1600_x4_avx2",
  ([(*args*)
     ("bitstate_in", "uint64_t[static 100]", (*is const?*)"false");
     ("rc_pointer", "const uint64_t[static 24]", (*is const?*)"true");
     ("rho8_ptr", "const uint64_t[static 4]", (*is const?*)"true");
     ("rho56_ptr", "const uint64_t[static 4]", (*is const?*)"true")],
   "void",
   [(* input buffers *)
    ("bitstate_in", "100"(* num elems *), 8(* elem bytesize *));
    ("rc_pointer", "24"(* num elems *), 8(* elem bytesize *));
    ("rho8_ptr", "4"(* num elems *), 8(* elem bytesize *));
    ("rho56_ptr", "4"(* num elems *), 8(* elem bytesize *))],
   [(* output buffers *)
    ("bitstate_in", "100"(* num elems *), 8(* elem bytesize *))],
   [(* temporary buffers *)
   ])
);

];;
