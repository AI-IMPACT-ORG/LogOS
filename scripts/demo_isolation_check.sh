#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "demo-isolation-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

scan_imports() {
  local pattern="$1"

  command -v rg >/dev/null 2>&1 || die "rg is required for this check"

  local out status
  set +e
  out="$(
    rg -n --hidden \
      --glob '*.agda' \
      --glob '*.lagda.md' \
      --glob '!_build/**' \
      --glob '!.git/**' \
      --glob '!.agda/**' \
      --glob '!**/Demo/**' \
      --glob '!**/Demos/**' \
      -- "${pattern}" . 2>&1
  )"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    out=""
  fi
  printf "%s" "${out}"
}

# Match only actual import lines to avoid comments/documentation.
DEMO_IMPORTS_PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+.*\\.(Demo|Demos)(\\.|$)'

bad_imports="$(scan_imports "${DEMO_IMPORTS_PATTERN}")"
if [[ -n "${bad_imports}" ]]; then
  die $'found demo-folder imports outside Demo/Demos directories:\n'"${bad_imports}"
fi

echo "demo-isolation-check: OK"
