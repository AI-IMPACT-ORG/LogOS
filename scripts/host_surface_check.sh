#!/usr/bin/env bash
# LogOS: an Agda Library for foundational logic architecture
# Copyright (C) 2025 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "host-surface-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# The "host surface" is the tiny set of modules allowed to import Agda's
# builtins / primitive universe machinery. Everything else should depend on
# these wrappers instead, making the library easier to port to other hosts.
HOST_SURFACE_FILES=(
  "Level.agda"
  "Data/Nat.agda"
  "Data/Bool.agda"
  "Data/List.agda"
  "Data/Maybe.agda"
  "Data/Relation/Binary/PropositionalEquality.agda"
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

  if command -v rg >/dev/null 2>&1; then
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
  else
    local out status
    set +e
    out="$(grep -RIn --include='*.agda' --exclude-dir='_build' -E -- "${pattern}" . 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'grep error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  fi
}

# Match only actual import lines to avoid comments/documentation.
HOST_IMPORTS_PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+Agda\\.(Builtin\\.|Primitive\\b)'

bad_imports="$(scan_imports "${HOST_IMPORTS_PATTERN}" | filter_host_surface)"
if [[ -n "${bad_imports}" ]]; then
  die $'found direct Agda host imports outside the host surface:\n'"${bad_imports}"$'\n\n'"Allowed host surface files:"$'\n'"$(printf '  - %s\n' "${HOST_SURFACE_FILES[@]}")"
fi

echo "host-surface-check: OK"
