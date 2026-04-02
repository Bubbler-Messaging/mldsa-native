# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = unpack_sk_and_ntt_s1_poly_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = unpack_sk_and_ntt_s1_poly

DEFINES += -DMLD_CONFIG_REDUCE_RAM
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mldsa/src/sign.c

CHECK_FUNCTION_CONTRACTS=mld_unpack_sk_and_ntt_s1_poly
USE_FUNCTION_CONTRACTS=mld_unpack_sk
USE_FUNCTION_CONTRACTS+=mld_polyeta_unpack
USE_FUNCTION_CONTRACTS+=mld_poly_ntt
USE_FUNCTION_CONTRACTS+=mld_poly_pointwise_montgomery
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

FUNCTION_NAME = unpack_sk_and_ntt_s1_poly

# This function is large enough to need...
CBMC_OBJECT_BITS = 10

include ../Makefile.common
