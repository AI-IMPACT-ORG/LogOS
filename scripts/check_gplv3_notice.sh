#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="license-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
REPO_ROOT="$(cd "${LIB_ROOT}/.." && pwd)"

check_require_cmd "${CHECK_NAME}" rg

check_gplv3_notice() {
  local file="$1"

  [[ -f "$file" ]] || die "missing file: $file"
  [[ -s "$file" ]] || die "empty file: $file"

  grep -Fq "GNU GENERAL PUBLIC LICENSE" "$file" || die "not GPLv3: missing title in $file"
  grep -Fq "Version 3, 29 June 2007" "$file" || die "not GPLv3: missing version line in $file"
  grep -Fq "Copyright (C) 2007 Free Software Foundation, Inc." "$file" \
    || die "missing FSF copyright notice in $file"
}

check_gplv3_notice "${LIB_ROOT}/LICENSE"

# If the library lives inside a larger repository, keep root and library licenses in sync.
if [[ -f "${REPO_ROOT}/LICENSE" ]]; then
  check_gplv3_notice "${REPO_ROOT}/LICENSE"
  cmp -s "${REPO_ROOT}/LICENSE" "${LIB_ROOT}/LICENSE" \
    || die "root LICENSE differs from ${LIB_ROOT}/LICENSE (keep them identical)"
fi

# Library declares SPDX tag in README (keep it simple/robust: accept either form).
if [[ -f "${LIB_ROOT}/README.md" ]]; then
  out=""
  status=0
  set +e
  out="$(rg -q "GPL-3\\.0-only|GPLv3" "${LIB_ROOT}/README.md" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -ne 0 ]]; then
    die "missing GPL notice in ${LIB_ROOT}/README.md (expected GPL-3.0-only or GPLv3)"
  fi
fi

echo "license-check: OK"

