#!/usr/bin/env bash
# LogOS: an Agda research library for foundational logic system architecture.
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "legacy-isolation-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

bad=""

for f in LogOS/Packs/*/All.agda; do
  [[ -f "$f" ]] || continue

  if command -v rg >/dev/null 2>&1; then
    out="$(rg -n '^(open import|import)[[:space:]]+.*Legacy' "$f" || true)"
  else
    out="$(grep -nE '^(open import|import)[[:space:]]+.*Legacy' "$f" 2>/dev/null || true)"
  fi

  if [[ -n "$out" ]]; then
    bad+="${f}:"$'\n'"${out}"$'\n'
  fi
done

if [[ -n "$bad" ]]; then
  die $'curated pack entrypoints must not import Legacy modules:\n'"${bad}"
fi

echo "legacy-isolation-check: OK"

