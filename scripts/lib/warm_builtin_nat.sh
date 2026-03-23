#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

if [[ "$#" -ne 5 ]]; then
  echo "usage: warm_builtin_nat.sh <agda> <agda_flags> <agda_warn_flags> <build_dir> <module_prefix>" >&2
  exit 2
fi

AGDA_BIN="$1"
AGDA_FLAGS_STR="$2"
AGDA_WARN_FLAGS_STR="$3"
BUILD_DIR="$4"
MODULE_PREFIX="$5"

MODULE_FILE="${BUILD_DIR}/PrimNatWarmup.agda"

mkdir -p "${BUILD_DIR}"

cat > "${MODULE_FILE}" <<EOF
{-# OPTIONS --safe #-}
module ${MODULE_PREFIX}.PrimNatWarmup where

import Agda.Builtin.Nat
EOF

read -r -a agda_flags <<< "${AGDA_FLAGS_STR}"
read -r -a agda_warn_flags <<< "${AGDA_WARN_FLAGS_STR}"

"${AGDA_BIN}" "${agda_flags[@]}" -i _build "${agda_warn_flags[@]}" "${MODULE_FILE}"
