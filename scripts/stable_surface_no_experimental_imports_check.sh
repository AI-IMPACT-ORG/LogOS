#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-no-experimental-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

shopt -s nullglob

FILES=(
  LogOS/Packs/*/All.agda
  LogOS/Packs/*/Core.agda
  LogOS/Packs/*/Kernel.agda
  LogOS/Packs/*/Surface.agda
)

IMPORT_EXPERIMENTAL_PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+.*\.Experimental(\.|$)'

bad=""

for f in "${FILES[@]}"; do
  [[ -f "$f" ]] || continue
  # Only enforce on stable surfaces (non-Experimental paths).
  if [[ "$f" == *"/Experimental/"* ]]; then
    continue
  fi

  if command -v rg >/dev/null 2>&1; then
    hit="$(rg -n -- "${IMPORT_EXPERIMENTAL_PATTERN}" "$f" || true)"
  else
    hit="$(grep -nE -- "${IMPORT_EXPERIMENTAL_PATTERN}" "$f" || true)"
    if [[ -n "${hit}" ]]; then
      hit="$(printf '%s\n' "${hit}" | sed "s|^|${f}:|")"
    fi
  fi

  if [[ -n "${hit}" ]]; then
    bad+="${hit}"$'\n'
  fi
done

if [[ -n "${bad}" ]]; then
  die $'found Experimental imports in stable pack surfaces:\n'"${bad}"
fi

echo "stable-surface-no-experimental-imports-check: OK"
