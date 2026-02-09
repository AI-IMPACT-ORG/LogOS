#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "doc-style-lint-check: $*" >&2
  exit 1
}

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

# This check relies on ripgrep’s stable regex + glob semantics.
command -v rg >/dev/null 2>&1 || die "rg is required for this check"

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

# NOTE: use grep-compatible regexes (portable; no PCRE features).
BANNED_REGEX='(truth[[:space:]]+after[[:space:]]+computation|least[[:space:]-]+fixed[[:space:]-]+point|definitional[[:space:]]+equality|decoded[[:space:]]+observational[[:space:]]+equality|post-fixed|meaning[[:space:]-]+preserving|semantic(s)?[[:space:]-]+preserving|semantic[[:space:]-]+equality|semantic[[:space:]-]+equivalence|same[[:space:]]+semantics|same[[:space:]]+meaning)'
OBS_EQUIV_REGEX='observational[[:space:]]+equivalence'
OBS_EQUALITY_REGEX='observational[[:space:]]+equality'

matches="$(rg_capture -n \
  --glob '*.md' \
  --glob '*.lagda.md' \
  --glob '*.tex' \
  --glob '*.agda' \
  --glob '!**/_build/**' \
  -- "${BANNED_REGEX}" "${DOC_ROOTS[@]}")"

# If the literature term “observational equivalence” is used, require the
# repo’s canonical term “observational equality” somewhere in the same file.
missing_obs=""
while IFS= read -r file; do
  [[ -z "$file" ]] && continue
  out=""
  status=0
  set +e
  out="$(rg -qi -- "${OBS_EQUALITY_REGEX}" "$file" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    missing_obs+="${file}"$'\n'
  fi
done < <(
  rg_capture -l -i \
    --glob '*.md' \
    --glob '*.lagda.md' \
    --glob '*.tex' \
    --glob '*.agda' \
    --glob '!**/_build/**' \
    -- "${OBS_EQUIV_REGEX}" "${DOC_ROOTS[@]}" | sort -u
)

if [ -n "$matches" ]; then
  echo "doc-style-lint-check: FAIL" >&2
  echo "Found banned drift phrases in prose-bearing files (docs and code comments):" >&2
  echo "$matches" >&2
  echo "Rewrite to canonical wording (e.g. \"least pre-fixed point\", \"observational equality\", \"judgmental equality\")." >&2
  exit 1
fi

if [ -n "$missing_obs" ]; then
  echo "doc-style-lint-check: FAIL" >&2
  echo "Files using \"observational equivalence\" must also include the canonical marker \"observational equality\":" >&2
  echo "$missing_obs" >&2
  exit 1
fi

echo "doc-style-lint-check: OK"
