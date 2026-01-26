#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

# LogOS policy check:
# stable pack entrypoints should not export “guardless”/raw claims such as
# `*_Without_Vacuity_Guards` or modules explicitly named `Guardless`.
#
# Rationale: stable surfaces are intended to be meaningfully interpretable without
# readers having to discover and add vacuity guards retroactively.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PATTERN='Without_Vacuity_Guards|module[[:space:]]+Guardless\b|\.Guardless\b'

stable_roots=()
while IFS= read -r allfile; do
  if grep -q "level = stable" "$allfile" 2>/dev/null; then
    stable_roots+=("$(dirname "$allfile")")
  fi
done < <(find LogOS/Packs -name 'All.agda' -print 2>/dev/null | sort)

if [ "${#stable_roots[@]}" -eq 0 ]; then
  echo "stable-surface-no-guardless-exports-check: OK (no stable packs found)"
  exit 0
fi

bad=""
for root in "${stable_roots[@]}"; do
  if command -v rg >/dev/null 2>&1; then
    out="$(rg -n "$PATTERN" "$root" \
      --glob '*.agda' \
      --glob '!**/Experimental/**' \
      --glob '!**/Legacy/**' \
      2>/dev/null || true)"
  else
    out="$(find "$root" -type f -name '*.agda' \
      ! -path '*/Experimental/*' \
      ! -path '*/Legacy/*' \
      -print0 2>/dev/null \
      | xargs -0 grep -nE "$PATTERN" 2>/dev/null || true)"
  fi

  if [ -n "$out" ]; then
    bad="${bad}${out}"$'\n'
  fi
done

if [ -n "$bad" ]; then
  echo "stable-surface-no-guardless-exports-check: FAIL" >&2
  echo "Found guardless/raw claim exports inside stable pack trees (excluding Legacy/Experimental):" >&2
  echo "$bad" >&2
  exit 1
fi

echo "stable-surface-no-guardless-exports-check: OK"
