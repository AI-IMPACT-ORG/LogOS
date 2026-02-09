#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

# LogOS policy check:
# If a documentation file (docs/ or LogOS/*.md) uses analogy-heavy vocabulary (RG/thermo/CFT/etc),
# require an explicit “Interpretation (analogy)” / “Analogy / interpretation”
# marker somewhere in that file.
#
# Rationale: keep the docs mechanically honest and avoid accidental reading of
# metaphors as literal theorems (especially for automated tooling).

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DOC_ROOTS=("docs" "LogOS")

TOKENS_REGEX='(\\bRG\\b|\\bCFT\\b|thermo|renormal|regulari[sz]e|holograph|Maxwell|black[[:space:]]+hole|physics|neural|transformer|LLM\\b)'
MARKER_REGEX='(Interpretation[[:space:]]*\\(analogy\\)|Analogy[[:space:]]*/[[:space:]]*interpretation|Interpretation[^\\n]*analogy)'

die() {
  echo "doc-analogy-markers-check: $*" >&2
  exit 1
}

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

has_root=0
for root in "${DOC_ROOTS[@]}"; do
  if [ -d "$root" ]; then
    has_root=1
    break
  fi
done

if [ "$has_root" -eq 0 ]; then
  echo "doc-analogy-markers-check: OK (no docs roots found)"
  exit 0
fi

bad=""

while IFS= read -r file; do
  [[ -z "$file" ]] && continue
  out=""
  status=0
  set +e
  out="$(rg -iq -- "$MARKER_REGEX" "$file" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    bad="${bad}${file}"$'\n'
  fi
done < <(
  rg_capture -l -i \
    --glob '*.md' \
    --glob '*.lagda.md' \
    --glob '!**/_build/**' \
    -- "$TOKENS_REGEX" "${DOC_ROOTS[@]}" | sort -u
)

if [ -n "$bad" ]; then
  echo "doc-analogy-markers-check: FAIL" >&2
  echo "The following docs use analogy-heavy tokens but do not include an explicit analogy marker:" >&2
  echo "$bad" >&2
  echo "Add a short marker such as \"Interpretation (analogy):\" or \"Analogy / interpretation:\"." >&2
  exit 1
fi

echo "doc-analogy-markers-check: OK"
