#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="metamath-mmc-build"
SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/../lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

REPO_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${REPO_ROOT}"

check_require_cmd "${CHECK_NAME}" ghc
GHC_FLAGS=(
  -Wall
  -Werror
  -O2
)

SRC_DIR="${REPO_ROOT}/tools/metamath/mmc"
OUT_DIR="${REPO_ROOT}/_build/metamath/mmc"

mkdir -p "${OUT_DIR}/ghc"

ghc "${GHC_FLAGS[@]}" \
  -i"${SRC_DIR}" \
  --make "${SRC_DIR}/Main.hs" \
  -outputdir "${OUT_DIR}/ghc" \
  -o "${OUT_DIR}/mmc"

echo "Wrote: ${OUT_DIR}/mmc"
