#!/usr/bin/env bash
# LogOS: an Agda research library for foundational logic system architecture.
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "kernel-antisymmetry-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# Enforce explicit intent for antisymmetry usage in the kernel.
# Any mention of PartialOrder/BulkBoundaryPO/antisym must be tagged with ANTISYM-OK.
ANTISYM_PATTERN='(BulkBoundaryPO|PartialOrder|po-bnd|antisym)'

scan_kernel() {
  local out status
  if command -v rg >/dev/null 2>&1; then
    set +e
    out="$(rg -n --glob 'LogOS/Kernel/**/*.agda' --glob '!_build/**' -- "${ANTISYM_PATTERN}" . 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'rg error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
  else
    set +e
    out="$(grep -RIn --include='*.agda' --exclude-dir='_build' -E -- "${ANTISYM_PATTERN}" LogOS/Kernel 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'grep error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
  fi
  printf "%s" "${out}"
}

hits="$(scan_kernel)"
if [[ -n "${hits}" ]]; then
  hits="$(printf "%s" "${hits}" | grep -v -E '^[^:]+:[0-9]+:[[:space:]]*--' || true)"
  hits="$(printf "%s" "${hits}" | grep -v -F "ANTISYM-OK" || true)"
fi

if [[ -n "${hits}" ]]; then
  die $'found kernel antisymmetry usage without ANTISYM-OK tag:\n'"${hits}"
fi

echo "kernel-antisymmetry-check: OK"
