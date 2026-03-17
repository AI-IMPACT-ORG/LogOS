#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="check-env"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

AGDA="${AGDA:-agda}"
PYTHON="${PYTHON:-python3}"

check_require_cmd "${CHECK_NAME}" "${AGDA}"
check_require_cmd "${CHECK_NAME}" "${PYTHON}"
check_require_cmd "${CHECK_NAME}" rg
check_require_cmd "${CHECK_NAME}" shellcheck
check_require_cmd "${CHECK_NAME}" make

echo "${CHECK_NAME}: required tools found"

echo
echo "Versions:"
echo "- agda: $(${AGDA} --version | head -n 1)"
echo "- python3: $(${PYTHON} --version 2>&1)"
echo "- rg: $(rg --version | head -n 1)"
echo "- shellcheck: $(shellcheck --version | rg -m 1 'version:' | sed 's/^.*version:[[:space:]]*//')"

echo
echo "Optional (Metamath mmc toolchain):"
if command -v ghc >/dev/null 2>&1 && command -v cabal >/dev/null 2>&1; then
  echo "- ghc: $(ghc --version | head -n 1)"
  echo "- cabal: $(cabal --version | head -n 1)"
else
  echo "- ghc/cabal: not found (only needed for tools/metamath/mmc)"
fi

echo
echo "Recommended gates:"
echo "- warm gate: make ci"
echo "- full gate: make check-all"

