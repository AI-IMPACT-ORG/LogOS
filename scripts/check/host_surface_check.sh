#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Builtins and primitive universe machinery are confined to `LogOS/Host/**`.
# - Everything else must depend on the curated host wrappers (also enforced for docs code blocks).

set -euo pipefail

CHECK_NAME="host-surface-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"

cd "${LIB_ROOT}"

# This check relies on ripgrep’s stable regex + glob semantics.
check_require_cmd "${CHECK_NAME}" rg

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

# The "host surface" is the minimal set of modules allowed to import Agda's
# builtins / primitive universe machinery. Everything else should depend on
# these wrappers instead, making the library easier to port to other hosts.
HOST_SURFACE_FILES=(
  "LogOS/Host/Level.agda"
  "LogOS/Host/Nat.agda"
  "LogOS/Host/Sum.agda"
  "LogOS/Host/Product.agda"
  "LogOS/Host/Empty.agda"
  "LogOS/Host/Relation/Binary/PropositionalEquality.agda"
)

# Per-wrapper host imports that are explicit and intentionally allowed.
ALLOWED_IMPORT_PATTERNS=(
  "LogOS/Host/Level.agda:^[[:space:]]*import[[:space:]]+Agda\\.Primitive([[:space:]]|$)"
  "LogOS/Host/Nat.agda:^[[:space:]]*open[[:space:]]+import[[:space:]]+Agda\\.Builtin\\.Nat([[:space:]]|$)"
  "LogOS/Host/Relation/Binary/PropositionalEquality.agda:^[[:space:]]*open[[:space:]]+import[[:space:]]+Agda\\.Builtin\\.Equality([[:space:]]|$)"
)

is_host_surface_import_allowed() {
  local file="$1"
  local line="$2"
  local entry pattern

  for entry in "${ALLOWED_IMPORT_PATTERNS[@]}"; do
    pattern="${entry#*:}"
    if [[ "$file" == "${entry%%:*}" ]]; then
      if printf '%s\n' "$line" | grep -Eq "$pattern"; then
        return 0
      fi
    fi
  done
  return 1
}

is_host_surface_file() {
  local file="$1"
  local f

  for f in "${HOST_SURFACE_FILES[@]}"; do
    if [[ "$file" == "$f" ]]; then
      return 0
    fi
  done
  return 1
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

raw_imports="$(scan_imports "${HOST_IMPORTS_PATTERN}")"
bad_imports=""
while IFS= read -r hit; do
  [[ -z "$hit" ]] && continue
  file="${hit%%:*}"
  file="${file#./}"
  rest="${hit#*:}"
  lineno="${rest%%:*}"
  line="${rest#*:}"
  if is_host_surface_file "$file"; then
    if ! is_host_surface_import_allowed "$file" "$line"; then
      bad_imports+="${file}:${lineno}:${line}"$'\n'
    fi
  else
    bad_imports+="${file}:${lineno}:${line}"$'\n'
  fi
done <<<"${raw_imports}"

if [[ -n "${bad_imports}" ]]; then
  die $'found direct Agda host imports outside the host surface or wrapper-intended imports:\n'"${bad_imports}"$'\n\n'"Allowed host surface files:"$'\n'"$(printf '  - %s\n' "${HOST_SURFACE_FILES[@]}")"
fi

# Docs parity: also forbid direct Agda host imports inside docs/*.md Agda code blocks.
docs_bad_imports="$(docs_scan_agda_blocks docs '*.md' | grep -E '^[^:]+:[0-9]+:[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+Agda\.(Builtin\.|Primitive)' || true)"
if [[ -n "${docs_bad_imports}" ]]; then
  die $'found direct Agda host imports in docs (Agda code blocks):\n'"${docs_bad_imports}"
fi

echo "host-surface-check: OK"
