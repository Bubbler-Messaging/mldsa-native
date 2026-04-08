// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "polyvec_lazy.h"

void harness(void)
{
  mld_poly *w;
  mld_polymat_eager *mat;
  unsigned int k;
  mld_polyvecl *v;
  mld_polyvecl_pointwise_acc_montgomery_eager(w, mat, k, v);
}
