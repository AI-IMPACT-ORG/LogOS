#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "honesty-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

scan() {
  local pattern="$1"
  shift
  local dirs=("$@")

  local out status
  set +e
  out="$(rg -n --glob '*.agda' --glob '!**/_build/**' -- "${pattern}" "${dirs[@]}" 2>&1)"
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

roots=(LogOS)
[[ -d Tests ]] && roots+=(Tests)
[[ -d Examples ]] && roots+=(Examples)

UNSAFE_OPT_PATTERN='^[[:space:]]*\{-# OPTIONS[^}]*--unsafe'
UNSOLVED_METAS_PATTERN='^[[:space:]]*\{-# OPTIONS[^}]*--allow-unsolved-metas'

unsafe_opts="$(scan "${UNSAFE_OPT_PATTERN}" "${roots[@]}")"
if [[ -n "${unsafe_opts}" ]]; then
  die $'found --unsafe in OPTIONS pragma:\n'"${unsafe_opts}"
fi

unsolved_metas="$(scan "${UNSOLVED_METAS_PATTERN}" "${roots[@]}")"
if [[ -n "${unsolved_metas}" ]]; then
  die $'found --allow-unsolved-metas in OPTIONS pragma:\n'"${unsolved_metas}"
fi

# Docs parity: scan Agda fenced code in literate docs too (no unsafe options).

docs_code="$(docs_scan_agda_blocks)"

docs_unsafe_opts="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\{-# OPTIONS[^}]*--unsafe' || true)"
if [[ -n "${docs_unsafe_opts}" ]]; then
  die $'found --unsafe in docs (Agda code blocks):\n'"${docs_unsafe_opts}"
fi

docs_unsolved_metas="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\{-# OPTIONS[^}]*--allow-unsolved-metas' || true)"
if [[ -n "${docs_unsolved_metas}" ]]; then
  die $'found --allow-unsolved-metas in docs (Agda code blocks):\n'"${docs_unsolved_metas}"
fi

echo "honesty-check: OK"
