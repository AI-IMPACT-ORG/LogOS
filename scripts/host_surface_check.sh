#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "host-surface-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# This check relies on ripgrep’s stable regex + glob semantics.
command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

# The "host surface" is the tiny set of modules allowed to import Agda's
# builtins / primitive universe machinery. Everything else should depend on
# these wrappers instead, making the library easier to port to other hosts.
HOST_SURFACE_FILES=(
  "LogOS/Host/Level.agda"
  "LogOS/Host/Nat.agda"
  "LogOS/Host/Bool.agda"
  "LogOS/Host/List.agda"
  "LogOS/Host/Maybe.agda"
  "LogOS/Host/String.agda"
  "LogOS/Host/Relation/Binary/PropositionalEquality.agda"
)

filter_host_surface() {
  local out
  out="$(cat)"
  for f in "${HOST_SURFACE_FILES[@]}"; do
    out="$(printf "%s" "$out" | grep -v -F "${f}:" || true)"
  done
  printf "%s" "$out"
}

scan_imports() {
  local pattern="$1"

  local out status
  set +e
  out="$(rg -n --glob '*.agda' --glob '!_build/**' -- "${pattern}" . 2>&1)"
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
HOST_IMPORTS_PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+Agda\.(Builtin\.|Primitive)'

bad_imports="$(scan_imports "${HOST_IMPORTS_PATTERN}" | filter_host_surface)"
if [[ -n "${bad_imports}" ]]; then
  die $'found direct Agda host imports outside the host surface:\n'"${bad_imports}"$'\n\n'"Allowed host surface files:"$'\n'"$(printf '  - %s\n' "${HOST_SURFACE_FILES[@]}")"
fi

# Docs parity: also forbid direct Agda host imports inside docs/*.lagda.md Agda code blocks.
docs_bad_imports="$(docs_scan_agda_blocks | grep -E '^[^:]+:[0-9]+:[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+Agda\.(Builtin\.|Primitive)' || true)"
if [[ -n "${docs_bad_imports}" ]]; then
  die $'found direct Agda host imports in docs (Agda code blocks):\n'"${docs_bad_imports}"
fi

echo "host-surface-check: OK"
