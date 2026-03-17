#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - High-risk polarity-sensitive modules must carry a `Direction note:` or
#   `Polarity note:` reminder near the module header.

set -euo pipefail

CHECK_NAME="polarity-reminder-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

files=(
  "LogOS/LT/Flow.agda"
  "LogOS/LT/Reflection.agda"
  "LogOS/Ports/IO.agda"
  "LogOS/Ports/Valuation/QAdapterBudgetTransport.agda"
)

violations=""
for path in "${files[@]}"; do
  [[ -f "${path}" ]] || die "missing target file: ${path}"
  if ! rg -q 'Direction note:|Polarity note:' "${path}"; then
    violations+=$'\n'"  - ${path}"
  fi
done

if [[ -n "${violations}" ]]; then
  die "missing polarity reminder block in required modules:${violations}"
fi

echo "${CHECK_NAME}: OK"
