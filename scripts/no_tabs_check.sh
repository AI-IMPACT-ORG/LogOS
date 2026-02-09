#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "no-tabs-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

TAB=$'\t'

scan_tabs() {
  command -v rg >/dev/null 2>&1 || die "rg is required for this check"

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
