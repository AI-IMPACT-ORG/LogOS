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
bad_any=""
allowed_prefix="LogOS/Domain/Legacy/"

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

# Global isolation: Legacy imports must stay inside the legacy namespace.
if command -v rg >/dev/null 2>&1; then
  while IFS= read -r f; do
    out="$(rg -n '^(open import|import)[[:space:]]+.*Legacy' "$f" || true)"
    [[ -n "$out" ]] || continue
    case "$f" in
      ${allowed_prefix}*) ;;
      *) bad_any+="${f}:"$'\n'"${out}"$'\n' ;;
    esac
  done < <(find LogOS -type f -name '*.agda' -not -path './_build/*' -print)
else
  while IFS= read -r f; do
    out="$(grep -nE '^(open import|import)[[:space:]]+.*Legacy' "$f" 2>/dev/null || true)"
    [[ -n "$out" ]] || continue
    case "$f" in
      ${allowed_prefix}*) ;;
      *) bad_any+="${f}:"$'\n'"${out}"$'\n' ;;
    esac
  done < <(find LogOS -type f -name '*.agda' -not -path './_build/*' -print)
fi

if [[ -n "$bad_any" ]]; then
  die $'Legacy imports must be confined to LogOS/Domain/Legacy:\n'"${bad_any}"
fi

echo "legacy-isolation-check: OK"
