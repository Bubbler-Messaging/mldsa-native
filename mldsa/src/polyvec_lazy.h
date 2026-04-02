/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
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
#define mld_s1vec_eager MLD_ADD_PARAM_SET(mld_s1vec_eager)
#define mld_s1vec_lazy MLD_ADD_PARAM_SET(mld_s1vec_lazy)
#define mld_s1vec MLD_ADD_PARAM_SET(mld_s1vec)
#define mld_s1vec_init_eager MLD_ADD_PARAM_SET(mld_s1vec_init_eager)
#define mld_s1vec_init_lazy MLD_ADD_PARAM_SET(mld_s1vec_init_lazy)
#define mld_s1vec_get_poly_eager MLD_ADD_PARAM_SET(mld_s1vec_get_poly_eager)
#define mld_s1vec_get_poly_lazy MLD_ADD_PARAM_SET(mld_s1vec_get_poly_lazy)
#define mld_s2vec_eager MLD_ADD_PARAM_SET(mld_s2vec_eager)
#define mld_s2vec_lazy MLD_ADD_PARAM_SET(mld_s2vec_lazy)
#define mld_s2vec MLD_ADD_PARAM_SET(mld_s2vec)
#define mld_s2vec_init_eager MLD_ADD_PARAM_SET(mld_s2vec_init_eager)
#define mld_s2vec_init_lazy MLD_ADD_PARAM_SET(mld_s2vec_init_lazy)
#define mld_s2vec_get_poly_eager MLD_ADD_PARAM_SET(mld_s2vec_get_poly_eager)
#define mld_s2vec_get_poly_lazy MLD_ADD_PARAM_SET(mld_s2vec_get_poly_lazy)
#define mld_t0vec_eager MLD_ADD_PARAM_SET(mld_t0vec_eager)
#define mld_t0vec_lazy MLD_ADD_PARAM_SET(mld_t0vec_lazy)
#define mld_t0vec MLD_ADD_PARAM_SET(mld_t0vec)
#define mld_t0vec_init_eager MLD_ADD_PARAM_SET(mld_t0vec_init_eager)
#define mld_t0vec_init_lazy MLD_ADD_PARAM_SET(mld_t0vec_init_lazy)
#define mld_t0vec_get_poly_eager MLD_ADD_PARAM_SET(mld_t0vec_get_poly_eager)
#define mld_t0vec_get_poly_lazy MLD_ADD_PARAM_SET(mld_t0vec_get_poly_lazy)
/* End of parameter set namespacing */

/* Eager: precompute and store full NTT'd vector */
typedef struct
{
  mld_polyvecl vec;
} mld_s1vec_eager;

typedef struct
{
  mld_polyveck vec;
} mld_s2vec_eager;

typedef struct
{
  mld_polyveck vec;
} mld_t0vec_eager;

/* Lazy: borrow packed data, unpack and NTT on demand */
typedef struct
{
  const uint8_t *packed;
} mld_s1vec_lazy;

typedef struct
{
  const uint8_t *packed;
} mld_s2vec_lazy;

typedef struct
{
  const uint8_t *packed;
} mld_t0vec_lazy;

/* s1vec */

#if !defined(MLD_CONFIG_REDUCE_RAM)
static MLD_INLINE void mld_s1vec_init_eager(
    mld_s1vec_eager *s1,
    const uint8_t packed_s1[MLDSA_L * MLDSA_POLYETA_PACKEDBYTES])
{
  mld_polyvecl_unpack_eta(&s1->vec, packed_s1);
  mld_polyvecl_ntt(&s1->vec);
}

static MLD_INLINE void mld_s1vec_get_poly_eager(mld_poly *buf,
                                                const mld_s1vec_eager *s1,
                                                unsigned int i)
{
  *buf = s1->vec.vec[i];
}
#else  /* !MLD_CONFIG_REDUCE_RAM */
static MLD_INLINE void mld_s1vec_init_lazy(
    mld_s1vec_lazy *s1,
    const uint8_t packed_s1[MLDSA_L * MLDSA_POLYETA_PACKEDBYTES])
{
  s1->packed = packed_s1;
}

static MLD_INLINE void mld_s1vec_get_poly_lazy(mld_poly *buf,
                                               const mld_s1vec_lazy *s1,
                                               unsigned int i)
{
  mld_polyeta_unpack(buf, s1->packed + i * MLDSA_POLYETA_PACKEDBYTES);
  mld_poly_ntt(buf);
}
#endif /* MLD_CONFIG_REDUCE_RAM */

/* s2vec */

#if !defined(MLD_CONFIG_REDUCE_RAM)
static MLD_INLINE void mld_s2vec_init_eager(
    mld_s2vec_eager *s2,
    const uint8_t packed_s2[MLDSA_K * MLDSA_POLYETA_PACKEDBYTES])
{
  mld_polyveck_unpack_eta(&s2->vec, packed_s2);
  mld_polyveck_ntt(&s2->vec);
}

static MLD_INLINE void mld_s2vec_get_poly_eager(mld_poly *buf,
                                                const mld_s2vec_eager *s2,
                                                unsigned int i)
{
  *buf = s2->vec.vec[i];
}
#else  /* !MLD_CONFIG_REDUCE_RAM */
static MLD_INLINE void mld_s2vec_init_lazy(
    mld_s2vec_lazy *s2,
    const uint8_t packed_s2[MLDSA_K * MLDSA_POLYETA_PACKEDBYTES])
{
  s2->packed = packed_s2;
}

static MLD_INLINE void mld_s2vec_get_poly_lazy(mld_poly *buf,
                                               const mld_s2vec_lazy *s2,
                                               unsigned int i)
{
  mld_polyeta_unpack(buf, s2->packed + i * MLDSA_POLYETA_PACKEDBYTES);
  mld_poly_ntt(buf);
}
#endif /* MLD_CONFIG_REDUCE_RAM */

/* t0vec */

#if !defined(MLD_CONFIG_REDUCE_RAM)
static MLD_INLINE void mld_t0vec_init_eager(
    mld_t0vec_eager *t0,
    const uint8_t packed_t0[MLDSA_K * MLDSA_POLYT0_PACKEDBYTES])
{
  mld_polyveck_unpack_t0(&t0->vec, packed_t0);
  mld_polyveck_ntt(&t0->vec);
}

static MLD_INLINE void mld_t0vec_get_poly_eager(mld_poly *buf,
                                                const mld_t0vec_eager *t0,
                                                unsigned int i)
{
  *buf = t0->vec.vec[i];
}
#else  /* !MLD_CONFIG_REDUCE_RAM */
static MLD_INLINE void mld_t0vec_init_lazy(
    mld_t0vec_lazy *t0,
    const uint8_t packed_t0[MLDSA_K * MLDSA_POLYT0_PACKEDBYTES])
{
  t0->packed = packed_t0;
}

static MLD_INLINE void mld_t0vec_get_poly_lazy(mld_poly *buf,
                                               const mld_t0vec_lazy *t0,
                                               unsigned int i)
{
  mld_polyt0_unpack(buf, t0->packed + i * MLDSA_POLYT0_PACKEDBYTES);
  mld_poly_ntt(buf);
}
#endif /* MLD_CONFIG_REDUCE_RAM */

/* Dispatch: typedef and define based on MLD_CONFIG_REDUCE_RAM */
#if defined(MLD_CONFIG_REDUCE_RAM)
typedef mld_s1vec_lazy mld_s1vec;
typedef mld_s2vec_lazy mld_s2vec;
typedef mld_t0vec_lazy mld_t0vec;
#define mld_s1vec_init mld_s1vec_init_lazy
#define mld_s1vec_get_poly mld_s1vec_get_poly_lazy
#define mld_s2vec_init mld_s2vec_init_lazy
#define mld_s2vec_get_poly mld_s2vec_get_poly_lazy
#define mld_t0vec_init mld_t0vec_init_lazy
#define mld_t0vec_get_poly mld_t0vec_get_poly_lazy
#else /* MLD_CONFIG_REDUCE_RAM */
typedef mld_s1vec_eager mld_s1vec;
typedef mld_s2vec_eager mld_s2vec;
typedef mld_t0vec_eager mld_t0vec;
#define mld_s1vec_init mld_s1vec_init_eager
#define mld_s1vec_get_poly mld_s1vec_get_poly_eager
#define mld_s2vec_init mld_s2vec_init_eager
#define mld_s2vec_get_poly mld_s2vec_get_poly_eager
#define mld_t0vec_init mld_t0vec_init_eager
#define mld_t0vec_get_poly mld_t0vec_get_poly_eager
#endif /* !MLD_CONFIG_REDUCE_RAM */

#endif /* !MLD_POLYVEC_LAZY_H */
