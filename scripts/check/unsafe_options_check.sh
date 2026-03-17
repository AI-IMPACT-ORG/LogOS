#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Forbid `--unsafe` and `--allow-unsolved-metas` in OPTIONS pragmas (also enforced in docs code blocks).

set -euo pipefail

CHECK_NAME="unsafe-options-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"

cd "${LIB_ROOT}"

check_require_cmd "${CHECK_NAME}" rg

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

# Markdown parity: scan Agda fenced code in all markdown files too (no unsafe options).

docs_code="$(docs_scan_agda_blocks . '*.md')"

docs_unsafe_opts="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\{-# OPTIONS[^}]*--unsafe' || true)"
if [[ -n "${docs_unsafe_opts}" ]]; then
  die $'found --unsafe in markdown (Agda code blocks):\n'"${docs_unsafe_opts}"
fi

docs_unsolved_metas="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\{-# OPTIONS[^}]*--allow-unsolved-metas' || true)"
if [[ -n "${docs_unsolved_metas}" ]]; then
  die $'found --allow-unsolved-metas in markdown (Agda code blocks):\n'"${docs_unsolved_metas}"
fi

echo "unsafe-options-check: OK"
