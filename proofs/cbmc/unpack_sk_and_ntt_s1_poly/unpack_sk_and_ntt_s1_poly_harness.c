// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

#include "sign.h"

void harness(void)
{
  mld_poly *buf, *cp;
  uint8_t *sk;
  unsigned int i;
  mld_unpack_sk_and_ntt_s1_poly(buf, sk, cp, i);
}
