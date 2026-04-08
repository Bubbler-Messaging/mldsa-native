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

/*
 * Eager and lazy variants of polynomial vector types.
 *
 * In eager mode, full vectors are precomputed and stored in memory.
 * In lazy mode, data is stored in packed form and expanded on demand,
 * trading computation for reduced memory usage.
 *
 * MLD_CONFIG_REDUCE_RAM selects which variant is used.
 */

#ifndef MLD_POLYVEC_LAZY_H
#define MLD_POLYVEC_LAZY_H

#include "poly.h"
#include "polyvec.h"

/* Parameter set namespacing */
#define mld_sk_s1hat_eager MLD_ADD_PARAM_SET(mld_sk_s1hat_eager)
#define mld_sk_s1hat_lazy MLD_ADD_PARAM_SET(mld_sk_s1hat_lazy)
#define mld_sk_s1hat MLD_ADD_PARAM_SET(mld_sk_s1hat)
#define mld_unpack_sk_s1hat_eager MLD_ADD_PARAM_SET(mld_unpack_sk_s1hat_eager)
#define mld_unpack_sk_s1hat_lazy MLD_ADD_PARAM_SET(mld_unpack_sk_s1hat_lazy)
#define mld_sk_s1hat_get_poly_eager \
  MLD_ADD_PARAM_SET(mld_sk_s1hat_get_poly_eager)
#define mld_sk_s1hat_get_poly_lazy MLD_ADD_PARAM_SET(mld_sk_s1hat_get_poly_lazy)
#define mld_sk_s2hat_eager MLD_ADD_PARAM_SET(mld_sk_s2hat_eager)
#define mld_sk_s2hat_lazy MLD_ADD_PARAM_SET(mld_sk_s2hat_lazy)
#define mld_sk_s2hat MLD_ADD_PARAM_SET(mld_sk_s2hat)
#define mld_unpack_sk_s2hat_eager MLD_ADD_PARAM_SET(mld_unpack_sk_s2hat_eager)
#define mld_unpack_sk_s2hat_lazy MLD_ADD_PARAM_SET(mld_unpack_sk_s2hat_lazy)
#define mld_sk_s2hat_get_poly_eager \
  MLD_ADD_PARAM_SET(mld_sk_s2hat_get_poly_eager)
#define mld_sk_s2hat_get_poly_lazy MLD_ADD_PARAM_SET(mld_sk_s2hat_get_poly_lazy)
#define mld_sk_t0hat_eager MLD_ADD_PARAM_SET(mld_sk_t0hat_eager)
#define mld_sk_t0hat_lazy MLD_ADD_PARAM_SET(mld_sk_t0hat_lazy)
#define mld_sk_t0hat MLD_ADD_PARAM_SET(mld_sk_t0hat)
#define mld_unpack_sk_t0hat_eager MLD_ADD_PARAM_SET(mld_unpack_sk_t0hat_eager)
#define mld_unpack_sk_t0hat_lazy MLD_ADD_PARAM_SET(mld_unpack_sk_t0hat_lazy)
#define mld_sk_t0hat_get_poly_eager \
  MLD_ADD_PARAM_SET(mld_sk_t0hat_get_poly_eager)
#define mld_sk_t0hat_get_poly_lazy MLD_ADD_PARAM_SET(mld_sk_t0hat_get_poly_lazy)
#define mld_polymat MLD_ADD_PARAM_SET(mld_polymat)
#define mld_polymat_eager MLD_ADD_PARAM_SET(mld_polymat_eager)
#define mld_polymat_lazy MLD_ADD_PARAM_SET(mld_polymat_lazy)
#define mld_polymat_get_row_eager MLD_ADD_PARAM_SET(mld_polymat_get_row_eager)
#define mld_polymat_get_poly_lazy MLD_ADD_PARAM_SET(mld_polymat_get_poly_lazy)
#define mld_polyvec_matrix_expand_eager \
  MLD_NAMESPACE_KL(polyvec_matrix_expand_eager)
#define mld_polyvec_matrix_expand_lazy \
  MLD_NAMESPACE_KL(polyvec_matrix_expand_lazy)
#define mld_polyvec_matrix_pointwise_montgomery_eager \
  MLD_NAMESPACE_KL(polyvec_matrix_pointwise_montgomery_eager)
#define mld_polyvec_matrix_pointwise_montgomery_lazy \
  MLD_NAMESPACE_KL(polyvec_matrix_pointwise_montgomery_lazy)
#define mld_polyvecl_pointwise_acc_montgomery_eager \
  MLD_NAMESPACE_KL(polyvecl_pointwise_acc_montgomery_eager)
#define mld_polyvecl_pointwise_acc_montgomery_lazy \
  MLD_NAMESPACE_KL(polyvecl_pointwise_acc_montgomery_lazy)
#define mld_poly_permute_bitrev_to_custom_optional \
  MLD_ADD_PARAM_SET(mld_poly_permute_bitrev_to_custom_optional)
/* End of parameter set namespacing */

/* Eager: precompute and store full NTT'd vector */
typedef struct
{
  mld_polyvecl vec;
} mld_sk_s1hat_eager;

typedef struct
{
  mld_polyveck vec;
} mld_sk_s2hat_eager;

typedef struct
{
  mld_polyveck vec;
} mld_sk_t0hat_eager;

/* Lazy: borrow packed data, unpack and NTT on demand */
typedef struct
{
  const uint8_t *packed;
} mld_sk_s1hat_lazy;

typedef struct
{
  const uint8_t *packed;
} mld_sk_s2hat_lazy;

typedef struct
{
  const uint8_t *packed;
} mld_sk_t0hat_lazy;

/* s1vec */

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_unpack_sk_s1hat_eager(
    mld_sk_s1hat_eager *s1,
    const uint8_t packed_s1[MLDSA_L * MLDSA_POLYETA_PACKEDBYTES])
{
  mld_polyvecl_unpack_eta(&s1->vec, packed_s1);
  mld_polyvecl_ntt(&s1->vec);
}

static MLD_INLINE void mld_sk_s1hat_get_poly_eager(mld_poly *buf,
                                                   const mld_sk_s1hat_eager *s1,
                                                   unsigned int i)
{
  *buf = s1->vec.vec[i];
}
#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */
#if defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_unpack_sk_s1hat_lazy(
    mld_sk_s1hat_lazy *s1,
    const uint8_t packed_s1[MLDSA_L * MLDSA_POLYETA_PACKEDBYTES])
{
  s1->packed = packed_s1;
}

static MLD_INLINE void mld_sk_s1hat_get_poly_lazy(mld_poly *buf,
                                                  const mld_sk_s1hat_lazy *s1,
                                                  unsigned int i)
{
  mld_polyeta_unpack(buf, s1->packed + i * MLDSA_POLYETA_PACKEDBYTES);
  mld_poly_ntt(buf);
}
#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

/* s2vec */

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_unpack_sk_s2hat_eager(
    mld_sk_s2hat_eager *s2,
    const uint8_t packed_s2[MLDSA_K * MLDSA_POLYETA_PACKEDBYTES])
{
  mld_polyveck_unpack_eta(&s2->vec, packed_s2);
  mld_polyveck_ntt(&s2->vec);
}

static MLD_INLINE void mld_sk_s2hat_get_poly_eager(mld_poly *buf,
                                                   const mld_sk_s2hat_eager *s2,
                                                   unsigned int i)
{
  *buf = s2->vec.vec[i];
}
#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */
#if defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_unpack_sk_s2hat_lazy(
    mld_sk_s2hat_lazy *s2,
    const uint8_t packed_s2[MLDSA_K * MLDSA_POLYETA_PACKEDBYTES])
{
  s2->packed = packed_s2;
}

static MLD_INLINE void mld_sk_s2hat_get_poly_lazy(mld_poly *buf,
                                                  const mld_sk_s2hat_lazy *s2,
                                                  unsigned int i)
{
  mld_polyeta_unpack(buf, s2->packed + i * MLDSA_POLYETA_PACKEDBYTES);
  mld_poly_ntt(buf);
}
#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

/* t0vec */

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_unpack_sk_t0hat_eager(
    mld_sk_t0hat_eager *t0,
    const uint8_t packed_t0[MLDSA_K * MLDSA_POLYT0_PACKEDBYTES])
{
  mld_polyveck_unpack_t0(&t0->vec, packed_t0);
  mld_polyveck_ntt(&t0->vec);
}

static MLD_INLINE void mld_sk_t0hat_get_poly_eager(mld_poly *buf,
                                                   const mld_sk_t0hat_eager *t0,
                                                   unsigned int i)
{
  *buf = t0->vec.vec[i];
}
#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */
#if defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_unpack_sk_t0hat_lazy(
    mld_sk_t0hat_lazy *t0,
    const uint8_t packed_t0[MLDSA_K * MLDSA_POLYT0_PACKEDBYTES])
{
  t0->packed = packed_t0;
}

static MLD_INLINE void mld_sk_t0hat_get_poly_lazy(mld_poly *buf,
                                                  const mld_sk_t0hat_lazy *t0,
                                                  unsigned int i)
{
  mld_polyt0_unpack(buf, t0->packed + i * MLDSA_POLYT0_PACKEDBYTES);
  mld_poly_ntt(buf);
}
#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

/* polymat */

/* Eager: precompute and store full matrix */
typedef struct
{
  mld_polyvecl vec[MLDSA_K];
} mld_polymat_eager;

/* Lazy: store seed, sample elements on demand.
 * poly_buffer holds the on-demand sampled matrix element A[k][l].
 * tmp is needed as scratch space for pointwise multiplication. */
typedef struct
{
  mld_poly poly_buffer;
  mld_poly tmp;
  uint8_t rho[MLDSA_SEEDBYTES];
} mld_polymat_lazy;

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
MLD_MUST_CHECK_RETURN_VALUE
static MLD_INLINE const mld_polyvecl *mld_polymat_get_row_eager(
    mld_polymat_eager *mat, unsigned int row)
{
  return &mat->vec[row];
}
#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

#if defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
static MLD_INLINE void mld_poly_permute_bitrev_to_custom_optional(mld_poly *p)
{
#if defined(MLD_USE_NATIVE_NTT_CUSTOM_ORDER)
  mld_poly_permute_bitrev_to_custom(p->coeffs);
#else
  (void)p;
#endif
}

MLD_MUST_CHECK_RETURN_VALUE
static MLD_INLINE const mld_poly *mld_polymat_get_poly_lazy(
    mld_polymat_lazy *mat, unsigned int k, unsigned int l)
{
  MLD_ALIGN uint8_t seed_ext[MLD_ALIGN_UP(MLDSA_SEEDBYTES + 2)];
  mld_memcpy(seed_ext, mat->rho, MLDSA_SEEDBYTES);
  seed_ext[MLDSA_SEEDBYTES + 0] = (uint8_t)l;
  seed_ext[MLDSA_SEEDBYTES + 1] = (uint8_t)k;
  mld_poly_uniform(&mat->poly_buffer, seed_ext);
  mld_poly_permute_bitrev_to_custom_optional(&mat->poly_buffer);
  /* @[FIPS204, Section 3.6.3] Destruction of intermediate values. */
  mld_zeroize(seed_ext, sizeof(seed_ext));
  return &mat->poly_buffer;
}
#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

#if !defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
/*************************************************
 * Name:        mld_polyvec_matrix_expand_eager
 *
 * Description: Implementation of ExpandA. Generates matrix A with uniformly
 *              random coefficients a_{i,j} by performing rejection
 *              sampling on the output stream of SHAKE128(rho|j|i)
 *
 * Arguments:   - mld_polymat_eager *mat: pointer to output matrix
 *              - const uint8_t rho[]: byte array containing seed rho
 **************************************************/
MLD_INTERNAL_API
void mld_polyvec_matrix_expand_eager(mld_polymat_eager *mat,
                                     const uint8_t rho[MLDSA_SEEDBYTES])
__contract__(
  requires(memory_no_alias(mat, sizeof(mld_polymat_eager)))
  requires(memory_no_alias(rho, MLDSA_SEEDBYTES))
  assigns(memory_slice(mat, sizeof(mld_polymat_eager)))
  ensures(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
    array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
);

/*************************************************
 * Name:        mld_polyvec_matrix_pointwise_montgomery_eager
 *
 * Description: Compute matrix-vector multiplication in NTT domain with
 *              pointwise multiplication and multiplication by 2^{-32}.
 *              Input matrix and vector must be in NTT domain representation.
 *
 *              The first input "mat" must be the output of
 *              polyvec_matrix_expand() and so have coefficients in [0, Q-1]
 *              inclusive.
 *
 *              The second input "v" is assumed to be output of an NTT, and
 *              hence must have coefficients bounded by [-9q+1, +9q-1]
 *              inclusive.
 *
 * Arguments:   - mld_polyveck *t: pointer to output vector t
 *              - mld_polymat_eager *mat: pointer to input matrix
 *              - const mld_polyvecl *v: pointer to input vector v
 **************************************************/
MLD_INTERNAL_API
void mld_polyvec_matrix_pointwise_montgomery_eager(mld_polyveck *t,
                                                   mld_polymat_eager *mat,
                                                   const mld_polyvecl *v)
__contract__(
  requires(memory_no_alias(t, sizeof(mld_polyveck)))
  requires(memory_no_alias(mat, sizeof(mld_polymat_eager)))
  requires(memory_no_alias(v, sizeof(mld_polyvecl)))
  requires(forall(k1, 0, MLDSA_K, forall(l1, 0, MLDSA_L,
                                         array_bound(mat->vec[k1].vec[l1].coeffs, 0, MLDSA_N, 0, MLDSA_Q))))
  requires(forall(l1, 0, MLDSA_L,
                  array_abs_bound(v->vec[l1].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  assigns(memory_slice(t, sizeof(mld_polyveck)))
  ensures(forall(k0, 0, MLDSA_K,
                 array_abs_bound(t->vec[k0].coeffs, 0, MLDSA_N, MLDSA_Q)))
);

/*************************************************
 * Name:        mld_polyvecl_pointwise_acc_montgomery_eager
 *
 * Description: Compute one row of the matrix-vector multiplication
 *              w = (A * v)[k] in NTT domain. The matrix is the eager
 *              precomputed matrix from mld_polyvec_matrix_expand_eager,
 *              the vector is in NTT domain.
 *
 *              Pointwise multiplies row k of A with v, accumulates,
 *              and multiplies by 2^{-32}. Dispatches to the native
 *              implementation when available.
 *
 * Arguments:   - mld_poly *w: pointer to output polynomial w (row k of A*v)
 *              - const mld_polymat_eager *mat: pointer to input matrix
 *              - unsigned int k: row index, must be < MLDSA_K
 *              - const mld_polyvecl *v: pointer to input vector v
 **************************************************/
MLD_INTERNAL_API
void mld_polyvecl_pointwise_acc_montgomery_eager(mld_poly *w,
                                                 const mld_polymat_eager *mat,
                                                 unsigned int k,
                                                 const mld_polyvecl *v)
__contract__(
  requires(memory_no_alias(w, sizeof(mld_poly)))
  requires(memory_no_alias(mat, sizeof(mld_polymat_eager)))
  requires(memory_no_alias(v, sizeof(mld_polyvecl)))
  requires(k < MLDSA_K)
  requires(forall(l0, 0, MLDSA_L,
                  array_bound(mat->vec[k].vec[l0].coeffs, 0, MLDSA_N, 0, MLDSA_Q)))
  requires(forall(l1, 0, MLDSA_L,
    array_abs_bound(v->vec[l1].coeffs, 0, MLDSA_N, MLD_NTT_BOUND)))
  assigns(memory_slice(w, sizeof(mld_poly)))
  ensures(array_abs_bound(w->coeffs, 0, MLDSA_N, MLDSA_Q))
);
#endif /* !MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

#if defined(MLD_CONFIG_REDUCE_RAM) || defined(MLD_UNIT_TEST)
MLD_INTERNAL_API
void mld_polyvec_matrix_expand_lazy(mld_polymat_lazy *mat,
                                    const uint8_t rho[MLDSA_SEEDBYTES]);

MLD_INTERNAL_API
void mld_polyvec_matrix_pointwise_montgomery_lazy(mld_polyveck *t,
                                                  mld_polymat_lazy *mat,
                                                  const mld_polyvecl *v);

/*************************************************
 * Name:        mld_polyvecl_pointwise_acc_montgomery_lazy
 *
 * Description: Compute one row of the matrix-vector multiplication
 *              w = (A * v)[k] in NTT domain. The matrix is sampled
 *              on-the-fly from mat->rho via per-element rejection
 *              sampling, the vector is in NTT domain.
 *
 *              Uses the internal mat->tmp scratch for the per-column
 *              pointwise products.
 *
 * Arguments:   - mld_poly *w: pointer to output polynomial w (row k of A*v)
 *              - mld_polymat_lazy *mat: pointer to (lazy) input matrix
 *              - unsigned int k: row index, must be < MLDSA_K
 *              - const mld_polyvecl *v: pointer to input vector v
 **************************************************/
MLD_INTERNAL_API
void mld_polyvecl_pointwise_acc_montgomery_lazy(mld_poly *w,
                                                mld_polymat_lazy *mat,
                                                unsigned int k,
                                                const mld_polyvecl *v);
#endif /* MLD_CONFIG_REDUCE_RAM || MLD_UNIT_TEST */

/* Dispatch: typedef and define based on MLD_CONFIG_REDUCE_RAM */
#if defined(MLD_CONFIG_REDUCE_RAM)
typedef mld_sk_s1hat_lazy mld_sk_s1hat;
typedef mld_sk_s2hat_lazy mld_sk_s2hat;
typedef mld_sk_t0hat_lazy mld_sk_t0hat;
typedef mld_polymat_lazy mld_polymat;
#define mld_unpack_sk_s1hat mld_unpack_sk_s1hat_lazy
#define mld_sk_s1hat_get_poly mld_sk_s1hat_get_poly_lazy
#define mld_unpack_sk_s2hat mld_unpack_sk_s2hat_lazy
#define mld_sk_s2hat_get_poly mld_sk_s2hat_get_poly_lazy
#define mld_unpack_sk_t0hat mld_unpack_sk_t0hat_lazy
#define mld_sk_t0hat_get_poly mld_sk_t0hat_get_poly_lazy
#define mld_polyvec_matrix_expand mld_polyvec_matrix_expand_lazy
#define mld_polyvec_matrix_pointwise_montgomery \
  mld_polyvec_matrix_pointwise_montgomery_lazy
#define mld_polyvecl_pointwise_acc_montgomery \
  mld_polyvecl_pointwise_acc_montgomery_lazy
#else /* MLD_CONFIG_REDUCE_RAM */
typedef mld_sk_s1hat_eager mld_sk_s1hat;
typedef mld_sk_s2hat_eager mld_sk_s2hat;
typedef mld_sk_t0hat_eager mld_sk_t0hat;
typedef mld_polymat_eager mld_polymat;
#define mld_unpack_sk_s1hat mld_unpack_sk_s1hat_eager
#define mld_sk_s1hat_get_poly mld_sk_s1hat_get_poly_eager
#define mld_unpack_sk_s2hat mld_unpack_sk_s2hat_eager
#define mld_sk_s2hat_get_poly mld_sk_s2hat_get_poly_eager
#define mld_unpack_sk_t0hat mld_unpack_sk_t0hat_eager
#define mld_sk_t0hat_get_poly mld_sk_t0hat_get_poly_eager
#define mld_polyvec_matrix_expand mld_polyvec_matrix_expand_eager
#define mld_polyvec_matrix_pointwise_montgomery \
  mld_polyvec_matrix_pointwise_montgomery_eager
#define mld_polyvecl_pointwise_acc_montgomery \
  mld_polyvecl_pointwise_acc_montgomery_eager
#endif /* !MLD_CONFIG_REDUCE_RAM */

#endif /* !MLD_POLYVEC_LAZY_H */
