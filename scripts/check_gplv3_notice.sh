#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "license-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${LIB_ROOT}/.." && pwd)"

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
  if command -v rg >/dev/null 2>&1; then
    readme_ok="$(rg -q "GPL-3\\.0-only|GPLv3" "${LIB_ROOT}/README.md" && echo yes || echo no)"
  else
    readme_ok="$(grep -Eq "GPL-3\\.0-only|GPLv3" "${LIB_ROOT}/README.md" && echo yes || echo no)"
  fi

  if [[ "$readme_ok" != "yes" ]]; then
    die "missing GPL notice in ${LIB_ROOT}/README.md (expected GPL-3.0-only or GPLv3)"
  fi
fi

echo "license-check: OK"
