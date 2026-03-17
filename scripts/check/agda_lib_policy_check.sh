#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The library file LogOS.agda-lib is part of the audited build surface.
# - Keep it minimal and pinned: `name: LogOS-LT`, `include: .`, and `flags: --safe` (exactly once each).

set -euo pipefail

CHECK_NAME="agda-lib-policy-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"

cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

LIB="LogOS.agda-lib"
[[ -f "${LIB}" ]] || die "missing ${LIB}"
[[ -s "${LIB}" ]] || die "empty ${LIB}"

rg_capture() {
  local out status
  set +e
  out="$(rg "$@" 2>&1)"
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

expect_single_line() {
  local label="$1"
  local pattern="$2"
  local got
  got="$(rg_capture -n -- "${pattern}" "${LIB}")"
  if [[ -z "${got}" ]]; then
    die "${LIB}: missing ${label} line"
  fi
  if [[ "$(printf "%s\n" "${got}" | wc -l | tr -d ' ')" != "1" ]]; then
    die "${LIB}: expected exactly one ${label} line, found:\n${got}"
  fi
}

expect_single_line "name: LogOS-LT" '^[[:space:]]*name:[[:space:]]*LogOS-LT[[:space:]]*$'
expect_single_line "include: ." '^[[:space:]]*include:[[:space:]]*[.][[:space:]]*$'

flags_lines="$(rg_capture -n -- '^[[:space:]]*flags:' "${LIB}")"
if [[ -z "${flags_lines}" ]]; then
  die "${LIB}: missing flags line (expected: flags: --safe)"
fi
if [[ "$(printf "%s\n" "${flags_lines}" | wc -l | tr -d ' ')" != "1" ]]; then
  die "${LIB}: expected exactly one flags line, found:\n${flags_lines}"
fi
if ! rg_capture -q -- '^[[:space:]]*flags:[[:space:]]*--safe[[:space:]]*$' "${LIB}" >/dev/null; then
  die "${LIB}: flags must be exactly '--safe'"
fi

echo "agda-lib-policy-check: OK"
