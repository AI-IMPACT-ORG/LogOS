#!/usr/bin/env bash
# LogOS: an Agda research library for foundational logic system architecture.
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "postulate-policy-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

extract_agda_blocks() {
  # Print Agda code lines inside ```agda fenced blocks, prefixed with file:line:.
  local file="$1"
  awk -v f="$file" '
    BEGIN { inside = 0 }
    /^[[:space:]]*```[[:space:]]*agda[[:space:]]*$/ { inside = 1; next }
    /^[[:space:]]*```[[:space:]]*$/ { if (inside == 1) { inside = 0; next } }
    inside == 1 { printf "%s:%d:%s\n", f, NR, $0 }
  ' "$file"
}

scan_docs_agda_blocks() {
  local out=""
  while IFS= read -r -d '' f; do
    out+=$(extract_agda_blocks "$f" || true)
    out+=$'\n'
  done < <(find docs -type f -name '*.lagda.md' -not -path './_build/*' -print0 2>/dev/null || true)
  printf "%s" "$out"
}

scan() {
  local pattern="$1"

  if command -v rg >/dev/null 2>&1; then
    local out status
    set +e
    out="$(rg -n --glob '*.agda' --glob '!_build/**' -- "${pattern}" . 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'rg error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  else
    local out status
    set +e
    out="$(grep -RIn --include='*.agda' --exclude-dir='_build' -E -- "${pattern}" . 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'grep error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  fi
}

ALLOW_RE=(
  '^(\./)?LogOS/.*/Demo/.*\.agda:'
  '^(\./)?LogOS/.*/Demos/.*\.agda:'
  '^(\./)?Models/.*/Demo/.*\.agda:'
  '^(\./)?Models/.*/Demos/.*\.agda:'
)

filter_allowlist() {
  local out
  out="$(cat)"
  for re in "${ALLOW_RE[@]}"; do
    out="$(printf "%s" "${out}" | grep -v -E "${re}" || true)"
  done
  printf "%s" "${out}"
}

POSTULATE_PATTERN='^[[:space:]]*postulate[[:space:]]*$|^[[:space:]]*postulate[[:space:]]'
postulates="$(scan "${POSTULATE_PATTERN}" | filter_allowlist)"
if [[ -n "${postulates}" ]]; then
  die $'found postulate outside allowed locations:\n'"${postulates}"$'\n\nAllowed:\n  - Models/**/Demo/**/*.agda\n  - Models/**/Demos/**/*.agda'
fi

# Docs parity: do not allow `postulate` in Agda fenced code blocks.

docs_postulates="$(scan_docs_agda_blocks | grep -E '^[^:]+:[0-9]+:[[:space:]]*postulate([[:space:]]|$)' || true)"
if [[ -n "${docs_postulates}" ]]; then
  die $'found postulate in docs (Agda code blocks):\n'"${docs_postulates}"
fi

echo "postulate-policy-check: OK"
