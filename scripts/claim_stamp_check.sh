#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="claim-stamp-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "$ROOT"

check_require_cmd "${CHECK_NAME}" rg

FORMAT_DOC="docs/Kernel/ClaimRegister.lagda.md"
REQUIRED_FILES=(
  "README.md"
  "docs/LogOS_Core_Spec.lagda.md"
  "docs/Applications/Complexity.lagda.md"
  "docs/Applications/InfoTheory.lagda.md"
)

if [ ! -f "$FORMAT_DOC" ]; then
  die "missing format doc: $FORMAT_DOC"
fi

rg -q --fixed-strings "Claim stamp sidecar format (CNL-lite):" "$FORMAT_DOC" \
  || die "missing format marker in $FORMAT_DOC"

for kind in LITERAL STABILISED REPRESENTATIONAL ANALOGY; do
  rg -q --fixed-strings "CLAIM-STAMP: ${kind} | anchor=" "$FORMAT_DOC" \
    || die "missing ${kind} format example in $FORMAT_DOC"
done

stamps="$(rg -n \
  --glob '*.md' \
  --glob '*.lagda.md' \
  --glob '!**/_build/**' \
  -- 'CLAIM-STAMP:' README.md docs || true)"

[ -n "$stamps" ] || die "no claim stamps found under README.md/docs"

STAMP_RE='^[[:space:]]*<!--[[:space:]]CLAIM-STAMP:[[:space:]](LITERAL|STABILISED|REPRESENTATIONAL|ANALOGY)[[:space:]]\|[[:space:]]anchor=[^|>#]+#[^|>]+[[:space:]]-->[[:space:]]*$'

invalid=""
while IFS= read -r line; do
  [ -n "$line" ] || continue
  file="${line%%:*}"
  rest="${line#*:}"
  lno="${rest%%:*}"
  text="${rest#*:}"
  if [[ ! "$text" =~ $STAMP_RE ]]; then
    invalid+="${file}:${lno}:${text}"$'\n'
  fi
done <<<"$stamps"

if [ -n "$invalid" ]; then
  echo "claim-stamp-check: FAIL" >&2
  echo "Malformed claim stamps (expected: <!-- CLAIM-STAMP: KIND | anchor=path#symbol -->):" >&2
  echo "$invalid" >&2
  exit 1
fi

missing=""
for file in "${REQUIRED_FILES[@]}"; do
  if [ ! -f "$file" ]; then
    missing+="${file} (missing file)"$'\n'
    continue
  fi
  if ! rg -q -- 'CLAIM-STAMP:' "$file"; then
    missing+="${file}"$'\n'
  fi
done

if [ -n "$missing" ]; then
  echo "claim-stamp-check: FAIL" >&2
  echo "Missing required claim stamps in high-risk docs:" >&2
  echo "$missing" >&2
  exit 1
fi

echo "claim-stamp-check: OK"
