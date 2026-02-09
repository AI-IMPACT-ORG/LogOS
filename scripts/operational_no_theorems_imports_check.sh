#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "operational-no-theorems-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Policy: operational layers must not depend on proof packages (`LogOS.Theorems.*`).
#
# Rationale: Ports/Adapters/Computation/Boundary should remain “theorem-free”
# so we can reuse them as infrastructure without importing proof kits.

IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
THEOREMS_IMPORT="${IMPORT_LINE}LogOS\\.Theorems\\."

TARGET_DIRS=(
  LogOS/Boundary
  LogOS/Ports
  LogOS/Adapters
  LogOS/Computation
)

bad=""
for dir in "${TARGET_DIRS[@]}"; do
  [[ -d "${dir}" ]] || continue

  out=""
  status=0
  set +e
  out="$(rg -n \
    --glob '*.agda' \
    --glob '!**/_build/**' \
    -- "${THEOREMS_IMPORT}" "${dir}" 2>&1)"
  status="$?"
  set -e

  if [[ "${status}" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "${status}" -eq 0 && -n "${out}" ]]; then
    bad+="${out}"$'\n'
  fi
done

if [[ -n "${bad}" ]]; then
  die $'found `LogOS.Theorems.*` imports in operational layers:\n'"${bad}"$'\n\nRule: Ports/Adapters/Computation/Boundary must not import `LogOS.Theorems.*`. Lower reusable lemma cores or move proofs upward to `LogOS/Theorems/*`.'
fi

echo "operational-no-theorems-imports-check: OK"

