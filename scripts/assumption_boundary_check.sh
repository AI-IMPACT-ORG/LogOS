#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "assumption-boundary-check: $*" >&2
  exit 1
}

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

fail=0

scan() {
  local pattern="$1"
  shift
  local roots=("$@")
  ((${#roots[@]})) || return 0

  local out status
  set +e
  out="$(rg -n --glob '*.agda' --glob '!**/_build/**' -- "${pattern}" "${roots[@]}" 2>&1)"
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

legacy_names="$(scan "FlowAssumptions|JClosureAssumptions" LogOS)"
if [[ -n "${legacy_names}" ]]; then
  printf "Assumption boundary lint: legacy closure-assumption names found:\n" >&2
  printf "%s\n" "${legacy_names}" >&2
  fail=1
fi

core_roots=()
for r in LogOS/Kernel LogOS/Boundary LogOS/Ports LogOS/Adapters; do
  [[ -d "$r" ]] && core_roots+=("$r")
done

ASSUMPTION_DECL_RE='^[[:space:]]*(record[[:space:]]+.*Assumptions\\b|module[[:space:]]+.*Assumptions\\b)'
core_assumption_decls="$(scan "${ASSUMPTION_DECL_RE}" "${core_roots[@]}")"
if [[ -n "${core_assumption_decls}" ]]; then
  printf "Assumption boundary lint: `Assumptions` declarations must live outside core layers:\n" >&2
  printf "%s\n" "${core_assumption_decls}" >&2
  fail=1
fi

IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
META_ASSUMPTION_IMPORT_RE="${IMPORT_LINE}LogOS\\.Theorems\\.Meta\\.Assumptions\\."
core_assumption_imports="$(scan "${META_ASSUMPTION_IMPORT_RE}" "${core_roots[@]}")"
if [[ -n "${core_assumption_imports}" ]]; then
  printf "Assumption boundary lint: core layers must not import meta assumptions directly:\n" >&2
  printf "%s\n" "${core_assumption_imports}" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  exit 1
fi

echo "assumption-boundary-check: OK"
