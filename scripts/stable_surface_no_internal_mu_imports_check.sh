#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

scan_agda() {
  local dir="$1"
  local pattern="$2"

  [[ -d "${dir}" ]] || return 0

  if command -v rg >/dev/null 2>&1; then
    rg -n --glob '*.agda' --glob '!_build/**' -- "${pattern}" "${dir}" || true
  else
    grep -RIn --include='*.agda' --exclude-dir='_build' -E -- "${pattern}" "${dir}" 2>/dev/null || true
  fi
}

scan_docs() {
  local pattern="$1"

  [[ -d "docs" ]] || return 0

  if command -v rg >/dev/null 2>&1; then
    rg -n --glob '*.lagda.md' --glob '!_build/**' -- "${pattern}" docs || true
  else
    grep -RIn --include='*.lagda.md' --exclude-dir='_build' -E -- "${pattern}" docs 2>/dev/null || true
  fi
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

