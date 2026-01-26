#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
  if command -v rg >/dev/null 2>&1; then
    local out status
    set +e
    out="$(rg -n --glob '*.agda' --glob '*.lagda.md' --glob '!_build/**' -- "${TAB}" . 2>&1)"
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
    out="$(grep -RIn --include='*.agda' --include='*.lagda.md' --exclude-dir='_build' -- "${TAB}" . 2>&1)"
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

bad_tabs="$(scan_tabs)"
if [[ -n "${bad_tabs}" ]]; then
  die $'found tab characters in Agda source / literate docs:\n'"${bad_tabs}"
fi

echo "no-tabs-check: OK"

