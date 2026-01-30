#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

# LogOS policy check:
# Documentation wording must stay mechanically honest by avoiding drift phrases
# that are easy to misread as stronger claims than the mechanized code supports.
#
# This is intentionally conservative: if a banned phrase is actually intended,
# rewrite it into the repo’s canonical wording and/or make hypotheses explicit.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DOC_ROOTS=("docs" "LogOS")

if [ ! -d "docs" ] && [ ! -d "LogOS" ]; then
  echo "doc-style-lint-check: OK (no docs roots found)"
  exit 0
fi

# NOTE: use grep-compatible regexes (portable; no PCRE features).
BANNED_REGEX='(truth[[:space:]]+after[[:space:]]+computation|least[[:space:]-]+fixed[[:space:]-]+point|definitional[[:space:]]+equality|decoded[[:space:]]+observational[[:space:]]+equality|post-fixed|meaning[[:space:]-]+preserving|semantic(s)?[[:space:]-]+preserving|semantic[[:space:]-]+equality|semantic[[:space:]-]+equivalence|same[[:space:]]+semantics|same[[:space:]]+meaning)'
OBS_EQUIV_REGEX='observational[[:space:]]+equivalence'
OBS_EQUALITY_REGEX='observational[[:space:]]+equality'

matches=""

while IFS= read -r file; do
  hit="$(grep -Ein "$BANNED_REGEX" "$file" 2>/dev/null || true)"
  if [ -n "$hit" ]; then
    matches="${matches}${file}"$'\n'"${hit}"$'\n\n'
  fi

  # If the literature term “observational equivalence” is used, require the
  # repo’s canonical term “observational equality” somewhere in the same file.
  if grep -Eiq "$OBS_EQUIV_REGEX" "$file" 2>/dev/null; then
    if ! grep -Eiq "$OBS_EQUALITY_REGEX" "$file" 2>/dev/null; then
      matches="${matches}${file}"$'\n'"observational equivalence: missing canonical \"observational equality\" marker"$'\n\n'
    fi
  fi
done < <(
  for root in "${DOC_ROOTS[@]}"; do
    if [ -d "$root" ]; then
      find "$root" -type f \( -name '*.md' -o -name '*.lagda.md' -o -name '*.tex' -o -name '*.agda' \) \
        -not -path '*/_build/*' -print 2>/dev/null
    fi
  done | sort
)

if [ -n "$matches" ]; then
  echo "doc-style-lint-check: FAIL" >&2
  echo "Found banned drift phrases in prose-bearing files (docs and code comments):" >&2
  echo "$matches" >&2
  echo "Rewrite to canonical wording (e.g. \"least pre-fixed point\", \"observational equality\", \"judgmental equality\")." >&2
  exit 1
fi

echo "doc-style-lint-check: OK"
