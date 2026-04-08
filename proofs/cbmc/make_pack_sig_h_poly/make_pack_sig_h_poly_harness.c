// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "packing.h"

void harness(void)
{
  uint8_t *sig;
  mld_poly *a0, *a1;
  unsigned int k, n;
  int r;
  r = mld_make_pack_sig_h_poly(sig, a0, a1, k, n);
}
