#!/usr/bin/env bash
# LogOS: an Agda Library for foundational logic architecture
# Copyright (C) 2025 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "doc-reference-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

DOCS=(README.md CHANGELOG.md CONTRIBUTING.md)

while IFS= read -r -d '' f; do
  DOCS+=("$f")
done < <(find docs -type f \( -name '*.lagda.md' -o -name '*.md' \) -print0 2>/dev/null || true)

while IFS= read -r -d '' f; do
  DOCS+=("$f")
done < <(find LogOS -type f -name '*.md' -print0 2>/dev/null || true)

if [[ "${#DOCS[@]}" -eq 0 ]]; then
  die "no markdown files found"
fi

is_path_like() {
  local s="$1"

  case "$s" in
    LogOS/*|Data/*|Tests/*|docs/*|scripts/*|.github/*) return 0 ;;
    *.agda|*.lagda.md|*.md|*.tex|*.sh|*.yml|*.yaml|*.json) return 0 ;;
    *) return 1 ;;
  esac
}

strip_fences() {
  # Print file content outside fenced code blocks.
  # Fences are lines beginning with ``` (language annotation allowed).
  awk '
    BEGIN { inside = 0 }
    /^```/ { inside = 1 - inside; next }
    inside == 0 { print }
  ' "$1"
}

bad=""
for doc in "${DOCS[@]}"; do
  [[ -f "$doc" ]] || continue

  while IFS= read -r tok; do
    # tok has the form `...`
    ref="${tok#\`}"
    ref="${ref%\`}"
    # Skip non-path inline code that contains whitespace (e.g. `Re s ≡ 1/2`).
    [[ "$ref" =~ [[:space:]] ]] && continue

    is_path_like "$ref" || continue

    check="$ref"
    # Handle light glob patterns by checking the non-glob prefix exists.
    if [[ "$check" == *'*'* || "$check" == *'{'* || "$check" == *'}'* ]]; then
      check="${check%%\**}"
      check="${check%%\{*}"
      check="${check%%\}*}"
      check="${check%/}"
      [[ -z "$check" ]] && continue
    fi

    if [[ ! -e "$check" ]]; then
      bad+="${doc}: \`${ref}\`"$'\n'
    fi
  done < <(strip_fences "$doc" | grep -oE '`[^`]+`' || true)
done

if [[ -n "$bad" ]]; then
  die $'missing referenced paths in markdown docs:\n'"${bad}"
fi

echo "doc-reference-check: OK"
