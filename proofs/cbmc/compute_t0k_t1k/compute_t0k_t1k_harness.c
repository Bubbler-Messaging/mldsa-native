// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "polyvec_lazy.h"
#include "sign.h"

void mld_compute_t0k_t1k(mld_poly *t0k, mld_poly *t1k, mld_poly *tk,
                         mld_polymat *mat, unsigned int k,
                         const mld_polyvecl *s1hat, const mld_poly *s2k);

void harness(void)
{
  mld_poly *t0k;
  mld_poly *t1k;
  mld_poly *tk;
  mld_polymat *mat;
  unsigned int k;
  mld_polyvecl *s1hat;
  mld_poly *s2k;

  mld_compute_t0k_t1k(t0k, t1k, tk, mat, k, s1hat, s2k);
}
