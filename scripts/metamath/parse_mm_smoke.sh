#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/../lib/check_common.sh"

CHECK_NAME="metamath-parse-mm-smoke"
die() { check_die "${CHECK_NAME}" "$*"; }

REPO_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${REPO_ROOT}"

check_require_cmd "${CHECK_NAME}" python3

mkdir -p _build/metamath
python3 -B tools/metamath/parse_mm/parse_mm.py \
  scripts/metamath/testdata/mini.mm \
  --out _build/metamath/mini.mm.json
