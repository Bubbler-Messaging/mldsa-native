/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

/* References
 * ==========
 *
 * - [FIPS204]
 *   FIPS 204 Module-Lattice-Based Digital Signature Standard
 *   National Institute of Standards and Technology
 *   https://csrc.nist.gov/pubs/fips/204/final
 */

#include "polyvec_lazy.h"

#include "debug.h"

/* This namespacing is not done at the top to avoid a naming conflict
 * with native backends, which are currently not yet namespaced. */
#define mld_polymat_permute_bitrev_to_custom \
  MLD_ADD_PARAM_SET(mld_polymat_permute_bitrev_to_custom)
#define mld_polyvecl_permute_bitrev_to_custom \
  MLD_ADD_PARAM_SET(mld_polyvecl_permute_bitrev_to_custom)
#define mld_polyvecl_pointwise_acc_montgomery_c \
  MLD_ADD_PARAM_SET(mld_polyvecl_pointwise_acc_montgomery_c)

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)

static void mld_polyvecl_permute_bitrev_to_custom(mld_polyvecl *v)
__contract__(
  /* We don't specify that this should be a permutation, but only
   * that it does not change the bound established at the end of
   * mld_polyvec_matrix_expand.
   */
  requires(memory_no_alias(v, sizeof(mld_polyvecl)))
  requires(forall(x, 0, MLDSA_L,
    array_bound(v->vec[x].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
  assigns(memory_slice(v, sizeof(mld_polyvecl)))
  ensures(forall(x, 0, MLDSA_L,
    array_bound(v->vec[x].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
{
#if defined(MLD_USE_NATIVE_NTT_CUSTOM_ORDER)
  unsigned i;
  for (i = 0; i < MLDSA_L; i++)
  __loop__(
     assigns(i, memory_slice(v, sizeof(mld_polyvecl)))
     invariant(i <= MLDSA_L)
     invariant(forall(x, 0, MLDSA_L,
       array_bound(v->vec[x].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
     decreases(MLDSA_L - i))
  {
    mld_poly_permute_bitrev_to_custom(v->vec[i].coeffs);
  }
#else  /* MLD_USE_NATIVE_NTT_CUSTOM_ORDER */
  /* Nothing to do */
  (void)v;
#endif /* !MLD_USE_NATIVE_NTT_CUSTOM_ORDER */
}

static void mld_polymat_permute_bitrev_to_custom(mld_polymat_eager *mat)
__contract__(
  /* We don't specify that this should be a permutation, but only
   * that it does not change the bound established at the end of
   * mld_polyvec_matrix_expand.
   */
  requires(memory_no_alias(mat, sizeof(mld_polymat_eager)))
  requires(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
    array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
  assigns(memory_slice(mat, sizeof(mld_polymat_eager)))
  ensures(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
    array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
)
{
  unsigned int i;
  for (i = 0; i < MLDSA_K; i++)
  __loop__(
    assigns(i, memory_slice(mat, sizeof(mld_polymat_eager)))
    invariant(i <= MLDSA_K)
    invariant(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
      array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    decreases(MLDSA_K - i))
  {
    mld_polyvecl_permute_bitrev_to_custom(&mat->vec[i]);
  }
}

MLD_INTERNAL_API
void mld_polyvec_matrix_expand_eager(mld_polymat_eager *mat,
                                     const uint8_t rho[MLDSA_SEEDBYTES])
{
  unsigned int i, j;
  /*
   * We generate four separate seed arrays rather than a single one to work
   * around limitations in CBMC function contracts dealing with disjoint slices
   * of the same parent object.
   */

  MLD_ALIGN uint8_t seed_ext[4][MLD_ALIGN_UP(MLDSA_SEEDBYTES + 2)];

  for (j = 0; j < 4; j++)
  __loop__(
    assigns(j, object_whole(seed_ext))
    invariant(j <= 4)
    decreases(4 - j)
  )
  {
    mld_memcpy(seed_ext[j], rho, MLDSA_SEEDBYTES);
  }

#if !defined(MLD_CONFIG_SERIAL_FIPS202_ONLY) && !defined(MLD_CONFIG_REDUCE_RAM)
  /* Sample 4 matrix entries a time. */
  for (i = 0; i < (MLDSA_K * MLDSA_L / 4) * 4; i += 4)
  __loop__(
    assigns(i, j, object_whole(seed_ext), memory_slice(mat, sizeof(mld_polymat_eager)))
    invariant(i <= (MLDSA_K * MLDSA_L / 4) * 4 && i % 4 == 0)
    /* vectors 0 .. i / MLDSA_L are completely sampled */
    invariant(forall(k1, 0, i / MLDSA_L, forall(l1, 0, MLDSA_L,
      array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    /* last vector is sampled up to i % MLDSA_L */
    invariant(forall(k2, i / MLDSA_L, i / MLDSA_L + 1, forall(l2, 0, i % MLDSA_L,
      array_bound(mat->vec[k2].vec[l2].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    decreases((MLDSA_K * MLDSA_L / 4) * 4 - i)
  )
  {
    for (j = 0; j < 4; j++)
    __loop__(
      assigns(j, object_whole(seed_ext))
      invariant(j <= 4)
      decreases(4 - j)
    )
    {
      uint8_t x = (uint8_t)((i + j) / MLDSA_L);
      uint8_t y = (uint8_t)((i + j) % MLDSA_L);

      seed_ext[j][MLDSA_SEEDBYTES + 0] = y;
      seed_ext[j][MLDSA_SEEDBYTES + 1] = x;
    }

    mld_poly_uniform_4x(&mat->vec[i / MLDSA_L].vec[i % MLDSA_L],
                        &mat->vec[(i + 1) / MLDSA_L].vec[(i + 1) % MLDSA_L],
                        &mat->vec[(i + 2) / MLDSA_L].vec[(i + 2) % MLDSA_L],
                        &mat->vec[(i + 3) / MLDSA_L].vec[(i + 3) % MLDSA_L],
                        seed_ext);
  }
#else  /* !MLD_CONFIG_SERIAL_FIPS202_ONLY && !MLD_CONFIG_REDUCE_RAM */
  i = 0;
#endif /* !(!MLD_CONFIG_SERIAL_FIPS202_ONLY && !MLD_CONFIG_REDUCE_RAM) */

  /* Entries omitted by the batch-sampling are sampled individually. */
  while (i < MLDSA_K * MLDSA_L)
  __loop__(
    assigns(i, object_whole(seed_ext), memory_slice(mat, sizeof(mld_polymat_eager)))
    invariant(i <= MLDSA_K * MLDSA_L)
    /* vectors 0 .. i / MLDSA_L are completely sampled */
    invariant(forall(k1, 0, i / MLDSA_L, forall(l1, 0, MLDSA_L,
      array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    /* last vector is sampled up to i % MLDSA_L */
    invariant(forall(k2, i / MLDSA_L, i / MLDSA_L + 1, forall(l2, 0, i % MLDSA_L,
      array_bound(mat->vec[k2].vec[l2].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
    decreases(MLDSA_K * MLDSA_L - i)
  )
  {
    uint8_t x = (uint8_t)(i / MLDSA_L);
    uint8_t y = (uint8_t)(i % MLDSA_L);
    mld_poly *this_poly = &mat->vec[i / MLDSA_L].vec[i % MLDSA_L];

    seed_ext[0][MLDSA_SEEDBYTES + 0] = y;
    seed_ext[0][MLDSA_SEEDBYTES + 1] = x;

    mld_poly_uniform(this_poly, seed_ext[0]);
    i++;
  }

  mld_polymat_permute_bitrev_to_custom(mat);

  /* @[FIPS204, Section 3.6.3] Destruction of intermediate values. */
  mld_zeroize(seed_ext, sizeof(seed_ext));
}

MLD_STATIC_TESTABLE void mld_polyvecl_pointwise_acc_montgomery_c(
    mld_poly *w, const mld_polyvecl *u, const mld_polyvecl *v)
__contract__(
  requires(memory_no_alias(w, sizeof(mld_poly)))
  requires(memory_no_alias(u, sizeof(mld_polyvecl)))
  requires(memory_no_alias(v, sizeof(mld_polyvecl)))
  requires(forall(l0, 0, MLDSA_L,
                  array_bound(u->vec[l0].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
  requires(forall(l1, 0, MLDSA_L,
    array_abs_bound(v->vec[l1].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  assigns(memory_slice(w, sizeof(mld_poly)))
  ensures(array_abs_bound(w->coeffs, 0, MLDSA_N, MLDSA_Q))
)
{
  unsigned int i, j;
  mld_assert_bound_2d(u->vec, MLDSA_L, MLDSA_N, 0, MLDSA_Q);
  mld_assert_abs_bound_2d(v->vec, MLDSA_L, MLDSA_N, MLD_NTT_BOUND);
  for (i = 0; i < MLDSA_N; i++)
  __loop__(
    assigns(i, j, memory_slice(w, sizeof(mld_poly)))
    invariant(i <= MLDSA_N)
    invariant(array_abs_bound(w->coeffs, 0, i, MLDSA_Q))
    decreases(MLDSA_N - i)
  )
  {
    int64_t t = 0;
    int32_t r;
    for (j = 0; j < MLDSA_L; j++)
    __loop__(
      assigns(j, t)
      invariant(j <= MLDSA_L)
      invariant(t >= -(int64_t)j*(MLDSA_Q - 1)*(MLD_NTT_BOUND - 1))
      invariant(t <= (int64_t)j*(MLDSA_Q - 1)*(MLD_NTT_BOUND - 1))
      decreases(MLDSA_L - j)
    )
    {
      t += (int64_t)u->vec[j].coeffs[i] * v->vec[j].coeffs[i];
    }

    r = mld_montgomery_reduce(t);
    w->coeffs[i] = r;
  }

  mld_assert_abs_bound(w->coeffs, MLDSA_N, MLDSA_Q);
}

MLD_INTERNAL_API
void mld_polyvecl_pointwise_acc_montgomery_eager(mld_poly *w,
                                                 const mld_polymat_eager *mat,
                                                 unsigned int k,
                                                 const mld_polyvecl *v)
{
  const mld_polyvecl *u = &mat->vec[k];
  mld_assert_bound_2d(u->vec, MLDSA_L, MLDSA_N, 0, MLDSA_Q);
  mld_assert_abs_bound_2d(v->vec, MLDSA_L, MLDSA_N, MLD_NTT_BOUND);
#if defined(MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L4) && \
    MLD_CONFIG_PARAMETER_SET == 44
  {
    int ret;
    ret = mld_polyvecl_pointwise_acc_montgomery_l4_native(
        w->coeffs, (const int32_t (*)[MLDSA_N])u->vec,
        (const int32_t (*)[MLDSA_N])v->vec);
    if (ret == MLD_NATIVE_FUNC_SUCCESS)
    {
      mld_assert_abs_bound(w->coeffs, MLDSA_N, MLDSA_Q);
      return;
    }
  }
#elif defined(MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L5) && \
    MLD_CONFIG_PARAMETER_SET == 65
  {
    int ret;
    ret = mld_polyvecl_pointwise_acc_montgomery_l5_native(
        w->coeffs, (const int32_t (*)[MLDSA_N])u->vec,
        (const int32_t (*)[MLDSA_N])v->vec);
    if (ret == MLD_NATIVE_FUNC_SUCCESS)
    {
      mld_assert_abs_bound(w->coeffs, MLDSA_N, MLDSA_Q);
      return;
    }
  }
#elif defined(MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L7) && \
    MLD_CONFIG_PARAMETER_SET == 87
  {
    int ret;
    ret = mld_polyvecl_pointwise_acc_montgomery_l7_native(
        w->coeffs, (const int32_t (*)[MLDSA_N])u->vec,
        (const int32_t (*)[MLDSA_N])v->vec);
    if (ret == MLD_NATIVE_FUNC_SUCCESS)
    {
      mld_assert_abs_bound(w->coeffs, MLDSA_N, MLDSA_Q);
      return;
    }
  }
#endif /* !(MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L4 && \
          MLD_CONFIG_PARAMETER_SET == 44) &&                       \
          !(MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L5 && \
          MLD_CONFIG_PARAMETER_SET == 65) &&                       \
          MLD_USE_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_L7 &&   \
          MLD_CONFIG_PARAMETER_SET == 87 */
  /* The first input is bounded by [0, Q-1] inclusive
   * The second input is bounded by [-9Q+1, 9Q-1] inclusive . Hence, we can
   * safely accumulate in 64-bits without intermediate reductions as
   * MLDSA_L * (MLD_NTT_BOUND-1) * (Q-1) < INT64_MAX
   *
   * The worst case is ML-DSA-87: 7 * (9Q-1) * (Q-1) < 2**52
   * (and likewise for negative values)
   */
  mld_polyvecl_pointwise_acc_montgomery_c(w, u, v);
}

MLD_INTERNAL_API
void mld_polyvec_matrix_pointwise_montgomery_eager(mld_polyveck *t,
                                                   mld_polymat_eager *mat,
                                                   const mld_polyvecl *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(v->vec, MLDSA_L, MLDSA_N, MLD_NTT_BOUND);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(t, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k0, 0, i,
                     array_abs_bound(t->vec[k0].coeffs, 0, MLDSA_N, MLDSA_Q)))
    decreases(MLDSA_K - i)
  )
  {
    mld_polyvecl_pointwise_acc_montgomery_eager(&t->vec[i], mat, i, v);
  }

  mld_assert_abs_bound_2d(t->vec, MLDSA_K, MLDSA_N, MLDSA_Q);
}

#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

#if defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)

MLD_INTERNAL_API
void mld_polyvec_matrix_expand_lazy(mld_polymat_lazy *mat,
                                    const uint8_t rho[MLDSA_SEEDBYTES])
{
  mld_memcpy(mat->rho, rho, MLDSA_SEEDBYTES);
}

MLD_INTERNAL_API
void mld_polyvec_matrix_pointwise_montgomery_lazy(mld_polyveck *t,
                                                  mld_polymat_lazy *mat,
                                                  const mld_polyvecl *v)
{
  unsigned int i;
  for (i = 0; i < MLDSA_K; ++i)
  {
    mld_polyvecl_pointwise_acc_montgomery_lazy(&t->vec[i], mat, i, v);
  }
}

MLD_INTERNAL_API
void mld_polyvecl_pointwise_acc_montgomery_lazy(mld_poly *w,
                                                mld_polymat_lazy *mat,
                                                unsigned int k,
                                                const mld_polyvecl *v)
{
  unsigned int l;
  const mld_poly *a_kl = mld_polymat_get_poly_lazy(mat, k, 0);
  mld_poly_pointwise_montgomery(w, a_kl, &v->vec[0]);
  for (l = 1; l < MLDSA_L; l++)
  {
    a_kl = mld_polymat_get_poly_lazy(mat, k, l);
    mld_poly_pointwise_montgomery(&mat->tmp, a_kl, &v->vec[l]);
    mld_poly_add(w, &mat->tmp);
  }
  mld_poly_reduce(w);
}

#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef mld_polymat_permute_bitrev_to_custom
#undef mld_polyvecl_permute_bitrev_to_custom
#undef mld_polyvecl_pointwise_acc_montgomery_c
