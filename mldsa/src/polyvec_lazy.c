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
    const mld_polyvecl *row = mld_polymat_get_row_eager(mat, i);
    mld_polyvecl_pointwise_acc_montgomery(&t->vec[i], row, v);
  }

  mld_assert_abs_bound_2d(t->vec, MLDSA_K, MLDSA_N, MLDSA_Q);
}

MLD_INTERNAL_API
int mld_polyvec_matrix_pointwise_montgomery_zvec_eager(mld_polyveck *w,
                                                       mld_polymat_eager *mat,
                                                       mld_zvec_eager *z,
                                                       mld_poly *scratch)
{
  /* The infinity-norm bound check on z and the NTT of z have already
   * been performed in mld_zvec_init_eager. */
  (void)scratch;
  mld_polyvec_matrix_pointwise_montgomery_eager(w, mat, &z->vec);
  return 0;
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
  unsigned int i, l;

  for (i = 0; i < MLDSA_K; ++i)
  {
    const mld_poly *a_kl = mld_polymat_get_poly_lazy(mat, i, 0);
    mld_poly_pointwise_montgomery(&t->vec[i], a_kl, &v->vec[0]);
    for (l = 1; l < MLDSA_L; ++l)
    {
      a_kl = mld_polymat_get_poly_lazy(mat, i, l);
      mld_poly_pointwise_montgomery(&mat->tmp, a_kl, &v->vec[l]);
      mld_poly_add(&t->vec[i], &mat->tmp);
    }
    mld_poly_reduce(&t->vec[i]);
  }
}

MLD_INTERNAL_API
int mld_polyvec_matrix_pointwise_montgomery_zvec_lazy(mld_polyveck *w,
                                                      mld_polymat_lazy *mat,
                                                      mld_zvec_lazy *z,
                                                      mld_poly *scratch)
{
  unsigned int k, l;

  for (l = 0; l < MLDSA_L; l++)
  {
    /* mld_zvec_get_poly_lazy unpacks z[l], performs the per-poly
     * infinity-norm bound check, and NTTs scratch in place. */
    if (mld_zvec_get_poly_lazy(scratch, z, l))
    {
      return MLD_ERR_FAIL;
    }
    for (k = 0; k < MLDSA_K; k++)
    {
      const mld_poly *a_kl = mld_polymat_get_poly_lazy(mat, k, l);
      if (l == 0)
      {
        mld_poly_pointwise_montgomery(&w->vec[k], a_kl, scratch);
      }
      else
      {
        mld_poly_pointwise_montgomery(&mat->tmp, a_kl, scratch);
        mld_poly_add(&w->vec[k], &mat->tmp);
      }
    }
  }
  mld_polyveck_reduce(w);
  return 0;
}

#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

/* To facilitate single-compilation-unit (SCU) builds, undefine all macros.
 * Don't modify by hand -- this is auto-generated by scripts/autogen. */
#undef mld_polymat_permute_bitrev_to_custom
#undef mld_polyvecl_permute_bitrev_to_custom
