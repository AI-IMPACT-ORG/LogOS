#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "api-no-axioms-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Policy:
# - API entrypoints should not directly import `LogOS.Axioms.*`, to keep the
#   “minimal safe core” story mechanically enforced.
# - The only sanctioned API entrypoint for axiom interfaces is `LogOS.API.Axioms`.

AXIOMS_API="LogOS/API/Axioms.agda"

# Match only actual import lines to avoid prose references.
IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
FORBIDDEN="${IMPORT_LINE}LogOS\\.Axioms(\\.|$)"

bad=""

out=""
status=0
set +e
out="$(rg -n --glob '*.agda' --glob '!**/_build/**' -- "${FORBIDDEN}" LogOS/API 2>&1)"
status="$?"
set -e
if [[ "$status" -eq 2 ]]; then
  die $'rg error:\n'"${out}"
fi
if [[ "$status" -eq 1 ]]; then
  out=""
fi
if [[ -n "${out}" ]]; then
  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    case "${line}" in
      "${AXIOMS_API}:"*) ;;
      *) bad+="${line}"$'\n' ;;
    esac
  done <<<"${out}"
fi

if [[ -n "${bad}" ]]; then
  die $'found forbidden direct `LogOS.Axioms.*` imports in API surfaces:\n'"${bad}"$'\n\nUse `LogOS.API.Axioms` (explicit axiom interface surface) instead.'
fi

echo "api-no-axioms-check: OK"
