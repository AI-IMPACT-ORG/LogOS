#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/../lib/check_common.sh"

CHECK_NAME="metamath-mmc-smoke"
die() { check_die "${CHECK_NAME}" "$*"; }

REPO_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${REPO_ROOT}"

check_require_cmd "${CHECK_NAME}" ghc

# Canonical optional tooling docs live under `tools/metamath/README.md`.
bash scripts/metamath/mmc_build.sh
mkdir -p _build/metamath

_build/metamath/mmc/mmc compile scripts/metamath/testdata/mini.mm \
  --out _build/metamath/mini_art \
  --check-proofs \
  --progress-every 1
