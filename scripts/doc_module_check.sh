#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "doc-module-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

DOCS=(README.md CONTRIBUTING.md)

while IFS= read -r -d '' f; do
  DOCS+=("$f")
done < <(find docs -type f \( -name '*.lagda.md' -o -name '*.md' \) -print0 2>/dev/null || true)

while IFS= read -r -d '' f; do
  DOCS+=("$f")
done < <(find LogOS -type f -name '*.md' -print0 2>/dev/null || true)

if [[ "${#DOCS[@]}" -eq 0 ]]; then
  die "no markdown files found"
fi

strip_fences() {
  # Print file content outside fenced code blocks.
  # Fences are lines beginning with ``` (language annotation allowed).
  awk '
    BEGIN { inside = 0 }
    /^```/ { inside = 1 - inside; next }
    inside == 0 { print }
  ' "$1"
}

is_path_like() {
  local s="$1"

  case "$s" in
    LogOS/*|Tests/*|docs/*|scripts/*|.github/*) return 0 ;;
    *.agda|*.lagda.md) return 0 ;;
    *) return 1 ;;
  esac
}

expected_module_of_path() {
  local path="$1"
  path="${path#./}"

  if [[ "$path" == *.lagda.md ]]; then
    path="${path%.lagda.md}"
  else
    path="${path%.agda}"
  fi

  printf '%s' "${path//\//.}"
}

actual_module_of_file() {
  local f="$1"

  # Scan for the first `module X where` line.
  # We deliberately ignore nested/anonymous modules.
  local line
  line="$(grep -m 1 -E '^[[:space:]]*module[[:space:]]+[A-Za-z0-9_.]+' "$f" || true)"
  if [[ -z "$line" ]]; then
    return 1
  fi

  # shellcheck disable=SC2001
  printf '%s' "$line" | sed -E 's/^[[:space:]]*module[[:space:]]+([A-Za-z0-9_.]+).*/\1/'
}

bad=""

for doc in "${DOCS[@]}"; do
  [[ -f "$doc" ]] || continue

  while IFS= read -r tok; do
    ref="${tok#\`}"
    ref="${ref%\`}"
    [[ "$ref" =~ [[:space:]] ]] && continue

    is_path_like "$ref" || continue
    [[ "$ref" == *.agda || "$ref" == *.lagda.md ]] || continue
    [[ -e "$ref" ]] || continue

    expected="$(expected_module_of_path "$ref")"
    actual="$(actual_module_of_file "$ref" || true)"

    if [[ -z "$actual" ]]; then
      bad+="${doc}: \`${ref}\` (cannot find module declaration)"$'\n'
      continue
    fi

    if [[ "$expected" != "$actual" ]]; then
      bad+="${doc}: \`${ref}\` (expected module ${expected}, found ${actual})"$'\n'
    fi
  done < <(strip_fences "$doc" | grep -oE '`[^`]+`' || true)
done

if [[ -n "$bad" ]]; then
  die $'Agda module-name mismatches for referenced files:\n'"${bad}"
fi

echo "doc-module-check: OK"
