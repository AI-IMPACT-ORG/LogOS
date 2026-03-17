#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Forbid tab characters in repository text sources to avoid invisible formatting drift in code and docs.

set -euo pipefail

CHECK_NAME="no-tabs-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"

cd "${LIB_ROOT}"

TAB=$'\t'

scan_tabs() {
  check_require_cmd "${CHECK_NAME}" rg

  local out status
  set +e
  out="$(
    rg -n --hidden --fixed-strings \
      --glob '*.agda' \
      --glob '*.lagda.md' \
      --glob '*.md' \
      --glob '*.sh' \
      --glob '*.yml' \
      --glob '*.yaml' \
      --glob '*.json' \
      --glob '*.tex' \
      --glob '*.cff' \
      --glob '*.agda-lib' \
      --glob '!_build/**' \
      --glob '!.git/**' \
      --glob '!.agda/**' \
      -- "${TAB}" . 2>&1
  )"
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

bad_tabs="$(scan_tabs)"
if [[ -n "${bad_tabs}" ]]; then
  die $'found tab characters in repo text sources:\n'"${bad_tabs}"
fi

echo "no-tabs-check: OK"
