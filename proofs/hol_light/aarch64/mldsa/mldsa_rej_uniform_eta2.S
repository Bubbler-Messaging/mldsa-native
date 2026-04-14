/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/*
 * Standalone assembly for mld_rej_uniform_eta2_asm for HOL Light proofs.
 * This file is assembled to produce the object file that
 * define_assert_from_elf reads to extract the bytecodes being verified.
 *
 * Source: dev/aarch64_opt/src/rej_uniform_eta2_asm.S
 */

#define MLDSA_N 256

.text
.balign 4

// uint64_t mld_rej_uniform_eta2_asm(int32_t *r, const uint8_t *buf,
//                                   unsigned buflen, const uint8_t *table);
.global mld_rej_uniform_eta2_asm
mld_rej_uniform_eta2_asm:
        sub     sp, sp, #0x240
        mov     x7, #0x1
        movk    x7, #0x2, lsl #16
        movk    x7, #0x4, lsl #32
        movk    x7, #0x8, lsl #48
        mov     v31.d[0], x7
        mov     x7, #0x10
        movk    x7, #0x20, lsl #16
        movk    x7, #0x40, lsl #32
        movk    x7, #0x80, lsl #48
        mov     v31.d[1], x7
        movi    v30.8h, #15
        mov     x8, sp
        mov     x7, x8
        mov     x11, #0
        eor     v16.16b, v16.16b, v16.16b
.Lzero:
        str     q16, [x7], #64
        str     q16, [x7, #-48]
        str     q16, [x7, #-32]
        str     q16, [x7, #-16]
        add     x11, x11, #32
        cmp     x11, #MLDSA_N
        b.lt    .Lzero
        mov     x7, x8
        mov     x9, #0
        mov     x4, #MLDSA_N
.Lloop:
        cmp     x9, x4
        b.hs    .Lcopy
        sub     x2, x2, #8
        ld1     {v0.8b}, [x1], #8
        movi    v26.8b, #0x0F
        and     v27.8b, v0.8b, v26.8b
        ushr    v28.8b, v0.8b, #4
        zip1    v26.8b, v27.8b, v28.8b
        zip2    v29.8b, v27.8b, v28.8b
        ushll   v16.8h, v26.8b, #0
        ushll   v17.8h, v29.8b, #0
        cmhi    v4.8h, v30.8h, v16.8h
        cmhi    v5.8h, v30.8h, v17.8h
        and     v4.16b, v4.16b, v31.16b
        and     v5.16b, v5.16b, v31.16b
        uaddlv  s20, v4.8h
        uaddlv  s21, v5.8h
        fmov    w12, s20
        fmov    w13, s21
        ldr     q24, [x3, x12, lsl #4]
        ldr     q25, [x3, x13, lsl #4]
        cnt     v4.16b, v4.16b
        cnt     v5.16b, v5.16b
        uaddlv  s20, v4.8h
        uaddlv  s21, v5.8h
        fmov    w12, s20
        fmov    w13, s21
        tbl     v16.16b, {v16.16b}, v24.16b
        tbl     v17.16b, {v17.16b}, v25.16b
        st1     {v16.8h}, [x7]
        add     x7, x7, x12, lsl #1
        st1     {v17.8h}, [x7]
        add     x7, x7, x13, lsl #1
        add     x12, x12, x13
        add     x9, x9, x12
        cmp     x2, #8
        b.hs    .Lloop
.Lcopy:
        cmp     x9, x4
        csel    x9, x9, x4, lo
        // Barrett reduction constants for mod 5
        movz    w7, #6554
        dup     v26.8h, w7
        movi    v27.8h, #5
        movi    v7.8h, #2
        mov     x11, #0
        mov     x7, x8
.Lcopy_loop:
        ldr     q16, [x7], #32
        ldr     q18, [x7, #-16]
        // Barrett reduction: val mod 5
        sqdmulh v28.8h, v16.8h, v26.8h
        mls     v16.8h, v28.8h, v27.8h
        sqdmulh v28.8h, v18.8h, v26.8h
        mls     v18.8h, v28.8h, v27.8h
        // eta - (val mod 5) = 2 - (val mod 5)
        sub     v16.8h, v7.8h, v16.8h
        sub     v18.8h, v7.8h, v18.8h
        // Sign-extend 16->32 bit
        sshll2  v17.4s, v16.8h, #0
        sshll   v16.4s, v16.4h, #0
        sshll2  v19.4s, v18.8h, #0
        sshll   v18.4s, v18.4h, #0
        str     q16, [x0], #64
        str     q17, [x0, #-48]
        str     q18, [x0, #-32]
        str     q19, [x0, #-16]
        add     x11, x11, #16
        cmp     x11, #MLDSA_N
        b.lt    .Lcopy_loop
        mov     x0, x9
        add     sp, sp, #0x240
        ret
