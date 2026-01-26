#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
  if grep -Eiq "$TOKENS_REGEX" "$file" 2>/dev/null; then
    if ! grep -Eiq "$MARKER_REGEX" "$file" 2>/dev/null; then
      bad="${bad}${file}"$'\n'
    fi
  fi
done < <(
  for root in "${DOC_ROOTS[@]}"; do
    if [ -d "$root" ]; then
      find "$root" -type f \( -name '*.md' -o -name '*.lagda.md' \) -print 2>/dev/null
    fi
  done | sort
)

if [ -n "$bad" ]; then
  echo "doc-analogy-markers-check: FAIL" >&2
  echo "The following docs use analogy-heavy tokens but do not include an explicit analogy marker:" >&2
  echo "$bad" >&2
  echo "Add a short marker such as \"Interpretation (analogy):\" or \"Analogy / interpretation:\"." >&2
  exit 1
fi

echo "doc-analogy-markers-check: OK"
