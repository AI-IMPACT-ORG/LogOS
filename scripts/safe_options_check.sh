#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "safe-options-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# Docs/paper describe the repository as `--safe` by default. Enforce that every
# Agda module and literate Agda module opts into `--safe`.

SAFE_PRAGMA='{-# OPTIONS --safe #-}'

missing=""

if command -v rg >/dev/null 2>&1; then
  out="$(rg --files-without-match -F "${SAFE_PRAGMA}" \
    --glob '*.agda' \
    --glob '*.lagda.md' \
    --glob '!_build/**' \
    . || true)"
  if [[ -n "${out}" ]]; then
    missing="${out}"
  fi
else
  while IFS= read -r -d '' f; do
    if ! grep -qF "${SAFE_PRAGMA}" "$f"; then
      missing+="${f#./}"$'\n'
    fi
  done < <(find . -type f \( -name '*.agda' -o -name '*.lagda.md' \) -not -path './_build/*' -print0)
fi

if [[ -n "${missing}" ]]; then
  die $'missing `{-# OPTIONS --safe #-}` pragma:\n'"${missing}"
fi

echo "safe-options-check: OK"

