# Copyright (c) The mlkem-native project authors
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
{ stdenv, fetchFromGitHub, writeText, ... }:
stdenv.mkDerivation rec {
  pname = "s2n_bignum";
  version = "bc5165085c04c37baf02acff5919006bb97f74dc";
  src = fetchFromGitHub {
    owner = "jakemas";
    repo = "s2n-bignum";
    rev = "${version}";
    hash = "sha256-pGi1lMPUo1nx35zF8JkRC6GcnpgtS80dd6MxYlvSKn4=";
  };
  setupHook = writeText "setup-hook.sh" ''
    export S2N_BIGNUM_DIR="$1"
  '';
  patches = [ ];
  dontBuild = true;
  installPhase = ''
    mkdir -p $out
    cp -a . $out/
  '';
}
