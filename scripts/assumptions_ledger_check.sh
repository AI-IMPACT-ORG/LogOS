#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "assumptions-ledger-check: $*" >&2
  exit 1
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Policy:
# If a theorem module imports a known assumption pack, it must surface the
# dependency explicitly via a nested `Assumptions` record or module.
#
# This prevents "hidden assumptions" where a theorem appears standalone but
# silently depends on a curated axiom bundle.

ASSUMPTION_IMPORT_RE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+LogOS\\.Theorems\\.Meta\\.Assumptions(\\.|[[:space:]]|$)'
LEDGER_RE='^[[:space:]]*(record[[:space:]]+Assumptions([^[:alnum:]_]|$)|module[[:space:]]+Assumptions([^[:alnum:]_]|$))'

rg_list_files() {
  local out status
  set +e
  out="$(rg -l "$@" 2>&1)"
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

rg_quiet() {
  local out status
  set +e
  out="$(rg -q "$@" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  return "$status"
}

find_assumption_importers() {
  rg_list_files --glob '*.agda' --glob '!**/_build/**' -- "${ASSUMPTION_IMPORT_RE}" LogOS/Theorems
}

has_ledger() {
  local file="$1"
  rg_quiet -- "${LEDGER_RE}" "$file"
}

bad=()
while IFS= read -r file; do
  [[ -z "$file" ]] && continue

  case "$file" in
    LogOS/Theorems/Meta/Assumptions.agda) continue ;;
    LogOS/Theorems/Meta/Assumptions/*) continue ;;
  esac

  if ! has_ledger "$file"; then
    bad+=("$file")
  fi
done < <(find_assumption_importers)

if ((${#bad[@]})); then
  printf "assumptions-ledger-check: missing `Assumptions` ledger in modules importing assumption packs:\n" >&2
  for f in "${bad[@]}"; do
    printf "  - %s\n" "$f" >&2
  done
  printf "\nRule: if a theorem module imports `LogOS.Theorems.Meta.Assumptions.*`, it must define either:\n  - `record Assumptions ...`  OR\n  - `module Assumptions where ...` / `module Assumptions = ...`\n" >&2
  exit 1
fi

echo "assumptions-ledger-check: OK"
