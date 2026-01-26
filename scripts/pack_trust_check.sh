#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "pack-trust-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# Docs claim that pack entrypoints export `packTrust : PackTrust`. Enforce that
# this is present in the core pack entrypoints (All/Core), experimental
# entrypoints (Experimental All/Core), and any pack-level kernel wiring modules.

shopt -s nullglob

FILES=(
  LogOS/Packs/*/All.agda
  LogOS/Packs/*/Core.agda
  LogOS/Packs/*/Kernel.agda
  LogOS/Packs/*/Experimental/All.agda
  LogOS/Packs/*/Experimental/Core.agda
  LogOS/Packs/*/Experimental/Kernel.agda
)

if ((${#FILES[@]} == 0)); then
  die "no pack entrypoints found"
fi

missing=""

for f in "${FILES[@]}"; do
  [[ -f "$f" ]] || continue

  if command -v rg >/dev/null 2>&1; then
    if ! rg -q '^[[:space:]]*packTrust[[:space:]]*:[[:space:]]*PackTrust' "$f"; then
      missing+="$f"$'\n'
    fi
  else
    if ! grep -qE '^[[:space:]]*packTrust[[:space:]]*:[[:space:]]*PackTrust' "$f"; then
      missing+="$f"$'\n'
    fi
  fi
done

if [[ -n "${missing}" ]]; then
  die $'missing `packTrust : PackTrust` in pack entrypoints:\n'"${missing}"
fi

echo "pack-trust-check: OK"
