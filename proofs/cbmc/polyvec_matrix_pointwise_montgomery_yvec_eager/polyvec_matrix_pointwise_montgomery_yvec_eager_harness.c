// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "polyvec_lazy.h"

void harness(void)
{
  mld_polyveck *w;
  mld_polymat_eager *mat;
  mld_yvec_eager *y;
  mld_polyvecl *scratch;
  mld_polyvec_matrix_pointwise_montgomery_yvec_eager(w, mat, y, scratch);
}
