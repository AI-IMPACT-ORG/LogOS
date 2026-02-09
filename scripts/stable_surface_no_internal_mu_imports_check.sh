#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-no-internal-mu-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

scan_agda() {
  local dir="$1"
  local pattern="$2"

  [[ -d "${dir}" ]] || return 0

  local out status
  set +e
  out="$(rg -n --glob '*.agda' --glob '!**/_build/**' -- "${pattern}" "${dir}" 2>&1)"
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

scan_docs() {
  local pattern="$1"

  [[ -d "docs" ]] || return 0

  local out status
  set +e
  out="$(rg -n --glob '*.lagda.md' --glob '!**/_build/**' -- "${pattern}" docs 2>&1)"
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

# Match only actual import lines to avoid prose references.
IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
FORBIDDEN="${IMPORT_LINE}(LogOS\\.Ports\\.Semantic\\.InterlinguaMu(\\.|$)|LogOS\\.Theorems\\.Boundary\\.MuFusion(\\.|$))"

bad=""
bad+=$(scan_agda "LogOS/API" "${FORBIDDEN}")
bad+=$(scan_agda "LogOS/Packs" "${FORBIDDEN}")
bad+=$(scan_docs "${FORBIDDEN}")

if [[ -n "${bad}" ]]; then
  die $'found forbidden direct imports:\n'"${bad}"$'\n\nUse the stable spines instead:\n- `LogOS.Ports.Semantic.Interoperability` (μ transport: `Limit`)\n- `LogOS.Theorems.Boundary.Stabilisation` (μ-fusion + continuity kit)'
fi

echo "stable-surface-no-internal-mu-imports-check: OK"
