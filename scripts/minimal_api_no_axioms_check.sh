#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "minimal-api-no-axioms-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

MINIMAL="LogOS/API/Minimal.agda"
if [[ ! -f "${MINIMAL}" ]]; then
  die "missing ${MINIMAL}"
fi

# Policy: the minimal, safe user entrypoint should not directly import any
# `LogOS.Axioms.*` modules. Models that need additional structure should depend
# on axiom interfaces explicitly in their own layer.
PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+LogOS\\.Axioms(\\.|$)'

out=""
status=0
set +e
out="$(rg -n -- "${PATTERN}" "${MINIMAL}" 2>&1)"
status="$?"
set -e
if [[ "$status" -eq 2 ]]; then
  die $'rg error:\n'"${out}"
fi
if [[ "$status" -eq 1 ]]; then
  out=""
fi

if [[ -n "${out}" ]]; then
  die $'found direct `LogOS.Axioms.*` import(s) in minimal API entrypoint:\n'"${out}"
fi

echo "minimal-api-no-axioms-check: OK"
