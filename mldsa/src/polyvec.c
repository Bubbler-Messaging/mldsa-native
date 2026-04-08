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

#include "polyvec.h"

#include "debug.h"
#include "polyvec_lazy.h"

/**************************************************************/
/************ Vectors of polynomials of length MLDSA_L **************/
/**************************************************************/
MLD_INTERNAL_API
void mld_polyvecl_uniform_gamma1(mld_polyvecl *v,
                                 const uint8_t seed[MLDSA_CRHBYTES],
                                 uint16_t nonce)
{
#if defined(MLD_CONFIG_SERIAL_FIPS202_ONLY)
  int i;
#endif

  /* Safety: nonce is at most ((UINT16_MAX - MLDSA_L) / MLDSA_L), and, hence,
   * this cast is safe. See MLD_NONCE_UB comment in sign.c. */
  nonce = (uint16_t)(MLDSA_L * nonce);
  /* Now, nonce <= UINT16_MAX - (MLDSA_L - 1), so the casts below are safe. */
#if defined(MLD_CONFIG_SERIAL_FIPS202_ONLY)
  for (i = 0; i < MLDSA_L; i++)
  {
    mld_poly_uniform_gamma1(&v->vec[i], seed, (uint16_t)(nonce + i));
  }
#else /* MLD_CONFIG_SERIAL_FIPS202_ONLY */
#if MLDSA_L == 4
  mld_poly_uniform_gamma1_4x(&v->vec[0], &v->vec[1], &v->vec[2], &v->vec[3],
                             seed, nonce, (uint16_t)(nonce + 1),
                             (uint16_t)(nonce + 2), (uint16_t)(nonce + 3));
#elif MLDSA_L == 5
  mld_poly_uniform_gamma1_4x(&v->vec[0], &v->vec[1], &v->vec[2], &v->vec[3],
                             seed, nonce, (uint16_t)(nonce + 1),
                             (uint16_t)(nonce + 2), (uint16_t)(nonce + 3));
  mld_poly_uniform_gamma1(&v->vec[4], seed, (uint16_t)(nonce + 4));
#elif MLDSA_L == 7
  mld_poly_uniform_gamma1_4x(&v->vec[0], &v->vec[1], &v->vec[2],
                             &v->vec[3 /* irrelevant */], seed, nonce,
                             (uint16_t)(nonce + 1), (uint16_t)(nonce + 2),
                             0xFF /* irrelevant */);
  mld_poly_uniform_gamma1_4x(&v->vec[3], &v->vec[4], &v->vec[5], &v->vec[6],
                             seed, (uint16_t)(nonce + 3), (uint16_t)(nonce + 4),
                             (uint16_t)(nonce + 5), (uint16_t)(nonce + 6));
#endif /* MLDSA_L == 7 */
#endif /* !MLD_CONFIG_SERIAL_FIPS202_ONLY */

  mld_assert_bound_2d(v->vec, MLDSA_L, MLDSA_N, -(MLDSA_GAMMA1 - 1),
                      MLDSA_GAMMA1 + 1);
}

MLD_INTERNAL_API
void mld_polyvecl_ntt(mld_polyvecl *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(v->vec, MLDSA_L, MLDSA_N, MLDSA_Q);

  for (i = 0; i < MLDSA_L; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyvecl)))
    invariant(i <= MLDSA_L)
    invariant(forall(k0, i, MLDSA_L, forall(k1, 0, MLDSA_N, v->vec[k0].coeffs[k1] == loop_entry(*v).vec[k0].coeffs[k1])))
    invariant(forall(k1, 0, i, array_abs_bound(v->vec[k1].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
    decreases(MLDSA_L - i))
  {
    mld_poly_ntt(&v->vec[i]);
  }

  mld_assert_abs_bound_2d(v->vec, MLDSA_L, MLDSA_N, MLD_NTT_BOUND);
}

MLD_INTERNAL_API
uint32_t mld_polyvecl_chknorm(const mld_polyvecl *v, int32_t bound)
{
  unsigned int i;
  uint32_t t = 0;
  mld_assert_bound_2d(v->vec, MLDSA_L, MLDSA_N, -MLD_REDUCE32_RANGE_MAX,
                      MLD_REDUCE32_RANGE_MAX);

  for (i = 0; i < MLDSA_L; ++i)
  __loop__(
    invariant(i <= MLDSA_L)
    invariant(t == 0 || t == 0xFFFFFFFF)
    invariant((t == 0) == forall(k1, 0, i, array_abs_bound(v->vec[k1].coeffs, 0, MLDSA_N, bound)))
    decreases(MLDSA_L - i)
  )
  {
    /* Reference: Leaks which polynomial violates the bound via a conditional.
     * We are more conservative to reduce the number of declassifications in
     * constant-time testing.
     */
    t |= mld_poly_chknorm(&v->vec[i], bound);
  }
  return t;
}

/**************************************************************/
/************ Vectors of polynomials of length MLDSA_K **************/
/**************************************************************/
MLD_INTERNAL_API
void mld_polyveck_reduce(mld_polyveck *v)
{
  unsigned int i;
  mld_assert_bound_2d(v->vec, MLDSA_K, MLDSA_N, INT32_MIN,
                      MLD_REDUCE32_DOMAIN_MAX);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k0, i, MLDSA_K, forall(k1, 0, MLDSA_N, v->vec[k0].coeffs[k1] == loop_entry(*v).vec[k0].coeffs[k1])))
    invariant(forall(k2, 0, i,
      array_bound(v->vec[k2].coeffs, 0, MLDSA_N, -MLD_REDUCE32_RANGE_MAX, MLD_REDUCE32_RANGE_MAX)))
    decreases(MLDSA_K - i)
  )
  {
    mld_poly_reduce(&v->vec[i]);
  }

  mld_assert_bound_2d(v->vec, MLDSA_K, MLDSA_N, -MLD_REDUCE32_RANGE_MAX,
                      MLD_REDUCE32_RANGE_MAX);
}

MLD_INTERNAL_API
void mld_polyveck_caddq(mld_polyveck *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLDSA_Q);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k0, i, MLDSA_K, forall(k1, 0, MLDSA_N, v->vec[k0].coeffs[k1] == loop_entry(*v).vec[k0].coeffs[k1])))
    invariant(forall(k1, 0, i, array_bound(v->vec[k1].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
    decreases(MLDSA_K - i))
  {
    mld_poly_caddq(&v->vec[i]);
  }

  mld_assert_bound_2d(v->vec, MLDSA_K, MLDSA_N, 0, MLDSA_Q);
}

MLD_INTERNAL_API
void mld_polyveck_sub(mld_polyveck *u, const mld_polyveck *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(u->vec, MLDSA_K, MLDSA_N, MLDSA_Q);
  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLDSA_Q);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(u, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k0, 0, i,
                     array_bound(u->vec[k0].coeffs, 0, MLDSA_N, INT32_MIN, MLD_REDUCE32_DOMAIN_MAX)))
    invariant(forall(k1, i, MLDSA_K,
             forall(n1, 0, MLDSA_N, u->vec[k1].coeffs[n1] == loop_entry(*u).vec[k1].coeffs[n1])))
    decreases(MLDSA_K - i))
  {
    mld_poly_sub(&u->vec[i], &v->vec[i]);
  }

  mld_assert_bound_2d(u->vec, MLDSA_K, MLDSA_N, INT32_MIN,
                      MLD_REDUCE32_DOMAIN_MAX);
}

MLD_INTERNAL_API
void mld_polyveck_shiftl(mld_polyveck *v)
{
  unsigned int i;
  mld_assert_bound_2d(v->vec, MLDSA_K, MLDSA_N, 0, 1 << 10);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k1, 0, i, array_bound(v->vec[k1].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
    invariant(forall(k1, i, MLDSA_K,
             forall(n1, 0, MLDSA_N, v->vec[k1].coeffs[n1] == loop_entry(*v).vec[k1].coeffs[n1])))
    decreases(MLDSA_K - i)
  )
  {
    mld_poly_shiftl(&v->vec[i]);
  }

  mld_assert_bound_2d(v->vec, MLDSA_K, MLDSA_N, 0, MLDSA_Q);
}

MLD_INTERNAL_API
void mld_polyveck_ntt(mld_polyveck *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLDSA_Q);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k0, i, MLDSA_K, forall(k1, 0, MLDSA_N, v->vec[k0].coeffs[k1] == loop_entry(*v).vec[k0].coeffs[k1])))
    invariant(forall(k1, 0, i, array_abs_bound(v->vec[k1].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
    decreases(MLDSA_K - i))
  {
    mld_poly_ntt(&v->vec[i]);
  }
  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLD_NTT_BOUND);
}

MLD_INTERNAL_API
void mld_polyveck_invntt_tomont(mld_polyveck *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLDSA_Q);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k0, i, MLDSA_K, forall(k1, 0, MLDSA_N, v->vec[k0].coeffs[k1] == loop_entry(*v).vec[k0].coeffs[k1])))
    invariant(forall(k1, 0, i, array_abs_bound(v->vec[k1].coeffs, 0, MLDSA_N, MLD_INTT_BOUND)))
    decreases(MLDSA_K - i))
  {
    mld_poly_invntt_tomont(&v->vec[i]);
  }

  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLD_INTT_BOUND);
}

MLD_INTERNAL_API
void mld_polyveck_pointwise_poly_montgomery(mld_polyveck *r, const mld_poly *a,
                                            const mld_polyveck *v)
{
  unsigned int i;
  mld_assert_abs_bound_2d(v->vec, MLDSA_K, MLDSA_N, MLD_NTT_BOUND);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(r, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k2, 0, i, array_abs_bound(r->vec[k2].coeffs, 0, MLDSA_N, MLDSA_Q)))
    decreases(MLDSA_K - i)
  )
  {
    mld_poly_pointwise_montgomery(&r->vec[i], a, &v->vec[i]);
  }
  mld_assert_abs_bound_2d(r->vec, MLDSA_K, MLDSA_N, MLDSA_Q);
}

MLD_INTERNAL_API
uint32_t mld_polyveck_chknorm(const mld_polyveck *v, int32_t bound)
{
  unsigned int i;
  uint32_t t = 0;
  mld_assert_bound_2d(v->vec, MLDSA_K, MLDSA_N, -MLD_REDUCE32_RANGE_MAX,
                      MLD_REDUCE32_RANGE_MAX);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    invariant(i <= MLDSA_K)
    invariant(t == 0 || t == 0xFFFFFFFF)
    invariant((t == 0) == forall(k1, 0, i, array_abs_bound(v->vec[k1].coeffs, 0, MLDSA_N, bound)))
    decreases(MLDSA_K - i)
  )
  {
    /* Reference: Leaks which polynomial violates the bound via a conditional.
     * We are more conservative to reduce the number of declassifications in
     * constant-time testing.
     */
    t |= mld_poly_chknorm(&v->vec[i], bound);
  }

  return t;
}

MLD_INTERNAL_API
void mld_polyveck_decompose(mld_polyveck *v1, mld_polyveck *v0)
{
  unsigned int i;
  mld_assert_bound_2d(v0->vec, MLDSA_K, MLDSA_N, 0, MLDSA_Q);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(v0, sizeof(mld_polyveck)), memory_slice(v1, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k1, 0, i,
                     array_bound(v1->vec[k1].coeffs, 0, MLDSA_N, 0, (MLDSA_Q-1)/(2*MLDSA_GAMMA2))))
    invariant(forall(k2, 0, i,
                     array_abs_bound(v0->vec[k2].coeffs, 0, MLDSA_N, MLDSA_GAMMA2+1)))
    invariant(forall(k3, i, MLDSA_K,
                     array_bound(v0->vec[k3].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
    decreases(MLDSA_K - i)
  )
  {
    mld_poly_decompose(&v1->vec[i], &v0->vec[i]);
  }

  mld_assert_bound_2d(v1->vec, MLDSA_K, MLDSA_N, 0,
                      (MLDSA_Q - 1) / (2 * MLDSA_GAMMA2));
  mld_assert_abs_bound_2d(v0->vec, MLDSA_K, MLDSA_N, MLDSA_GAMMA2 + 1);
}

MLD_INTERNAL_API
void mld_polyveck_use_hint(mld_polyveck *w, const mld_polyveck *u,
                           const mld_polyveck *h)
{
  unsigned int i;
  mld_assert_bound_2d(u->vec, MLDSA_K, MLDSA_N, 0, MLDSA_Q);
  mld_assert_bound_2d(h->vec, MLDSA_K, MLDSA_N, 0, 2);

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(w, sizeof(mld_polyveck)))
    invariant(i <= MLDSA_K)
    invariant(forall(k2, 0, i,
                     array_bound(w->vec[k2].coeffs, 0, MLDSA_N, 0,
                                 (MLDSA_Q - 1) / (2 * MLDSA_GAMMA2))))
    decreases(MLDSA_K - i)
  )
  {
    mld_poly_use_hint(&w->vec[i], &u->vec[i], &h->vec[i]);
  }

  mld_assert_bound_2d(w->vec, MLDSA_K, MLDSA_N, 0,
                      (MLDSA_Q - 1) / (2 * MLDSA_GAMMA2));
}

MLD_INTERNAL_API
void mld_polyveck_pack_w1(uint8_t r[MLDSA_K * MLDSA_POLYW1_PACKEDBYTES],
                          const mld_polyveck *w1)
{
  unsigned int i;
  mld_assert_bound_2d(w1->vec, MLDSA_K, MLDSA_N, 0,
                      (MLDSA_Q - 1) / (2 * MLDSA_GAMMA2));

  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(r, MLDSA_K * MLDSA_POLYW1_PACKEDBYTES))
    invariant(i <= MLDSA_K)
    decreases(MLDSA_K - i)
  )
  {
    mld_polyw1_pack(&r[i * MLDSA_POLYW1_PACKEDBYTES], &w1->vec[i]);
  }
}

MLD_INTERNAL_API
void mld_polyveck_pack_eta(uint8_t r[MLDSA_K * MLDSA_POLYETA_PACKEDBYTES],
                           const mld_polyveck *p)
{
  unsigned int i;
  mld_assert_abs_bound_2d(p->vec, MLDSA_K, MLDSA_N, MLDSA_ETA + 1);
  for (i = 0; i < MLDSA_K; ++i)
  __loop__(
    assigns(i, memory_slice(r, MLDSA_K * MLDSA_POLYETA_PACKEDBYTES))
    invariant(i <= MLDSA_K)
    decreases(MLDSA_K - i)
  )
  {
    mld_polyeta_pack(&r[i * MLDSA_POLYETA_PACKEDBYTES], &p->vec[i]);
  }
}

MLD_INTERNAL_API
void mld_polyvecl_pack_eta(uint8_t r[MLDSA_L * MLDSA_POLYETA_PACKEDBYTES],
                           const mld_polyvecl *p)
{
  unsigned int i;
  mld_assert_abs_bound_2d(p->vec, MLDSA_L, MLDSA_N, MLDSA_ETA + 1);
  for (i = 0; i < MLDSA_L; ++i)
  __loop__(
    assigns(i, memory_slice(r, MLDSA_L * MLDSA_POLYETA_PACKEDBYTES))
    invariant(i <= MLDSA_L)
    decreases(MLDSA_L - i)
  )
  {
    mld_polyeta_pack(&r[i * MLDSA_POLYETA_PACKEDBYTES], &p->vec[i]);
  }
}

MLD_INTERNAL_API
void mld_polyvecl_unpack_eta(
    mld_polyvecl *p, const uint8_t r[MLDSA_L * MLDSA_POLYETA_PACKEDBYTES])
{
  unsigned int i;
  for (i = 0; i < MLDSA_L; ++i)
  {
    mld_polyeta_unpack(&p->vec[i], r + i * MLDSA_POLYETA_PACKEDBYTES);
  }

  mld_assert_bound_2d(p->vec, MLDSA_L, MLDSA_N, MLD_POLYETA_UNPACK_LOWER_BOUND,
                      MLDSA_ETA + 1);
}

MLD_INTERNAL_API
void mld_polyvecl_unpack_z(mld_polyvecl *z,
                           const uint8_t r[MLDSA_L * MLDSA_POLYZ_PACKEDBYTES])
{
  unsigned int i;
  for (i = 0; i < MLDSA_L; ++i)
  {
    mld_polyz_unpack(&z->vec[i], r + i * MLDSA_POLYZ_PACKEDBYTES);
  }

  mld_assert_bound_2d(z->vec, MLDSA_L, MLDSA_N, -(MLDSA_GAMMA1 - 1),
                      MLDSA_GAMMA1 + 1);
}

MLD_INTERNAL_API
void mld_polyveck_unpack_eta(
    mld_polyveck *p, const uint8_t r[MLDSA_K * MLDSA_POLYETA_PACKEDBYTES])
{
  unsigned int i;
  for (i = 0; i < MLDSA_K; ++i)
  {
    mld_polyeta_unpack(&p->vec[i], r + i * MLDSA_POLYETA_PACKEDBYTES);
  }

  mld_assert_bound_2d(p->vec, MLDSA_K, MLDSA_N, MLD_POLYETA_UNPACK_LOWER_BOUND,
                      MLDSA_ETA + 1);
}

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
MLD_INTERNAL_API
void mld_polyveck_unpack_t0(mld_polyveck *p,
                            const uint8_t r[MLDSA_K * MLDSA_POLYT0_PACKEDBYTES])
{
  unsigned int i;
  for (i = 0; i < MLDSA_K; ++i)
  {
    mld_polyt0_unpack(&p->vec[i], r + i * MLDSA_POLYT0_PACKEDBYTES);
  }

  mld_assert_bound_2d(p->vec, MLDSA_K, MLDSA_N, -(1 << (MLDSA_D - 1)) + 1,
                      (1 << (MLDSA_D - 1)) + 1);
}
#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */
