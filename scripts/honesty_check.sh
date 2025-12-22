#!/usr/bin/env bash
# LogOS: an Agda Library for foundational logic architecture
# Copyright (C) 2025 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "honesty-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

WHITELIST_POSTULATE_FILES=(
)

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
  # Emit all Agda code lines from docs/*.lagda.md code blocks.
  local out=""
  while IFS= read -r -d '' f; do
    out+=$(extract_agda_blocks "$f" || true)
    out+=$'\n'
  done < <(find docs -type f -name '*.lagda.md' -not -path './_build/*' -print0 2>/dev/null || true)
  printf "%s" "$out"
}

filter_whitelist() {
  local out
  out="$(cat)"
  if ((${#WHITELIST_POSTULATE_FILES[@]})); then
    for f in "${WHITELIST_POSTULATE_FILES[@]}"; do
      out="$(printf "%s" "$out" | grep -v -F "${f}:" || true)"
    done
  fi
  printf "%s" "$out"
}

filter_demo_dirs() {
  # Demos may use `postulate`, but must never be imported from non-demo code.
  # Demo isolation is enforced separately by `demo_isolation_check.sh`.
  grep -v -E '/(Demo|Demos)/' || true
}

scan() {
  local pattern="$1"
  shift
  local dirs=("$@")

  if command -v rg >/dev/null 2>&1; then
    local out status
    set +e
    out="$(rg -n --glob '*.agda' -- "${pattern}" "${dirs[@]}" 2>&1)"
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
    out="$(grep -RIn --include='*.agda' -E -- "${pattern}" "${dirs[@]}" 2>&1)"
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

postulates="$(scan '^[[:space:]]*postulate[[:space:]]*$|^[[:space:]]*postulate[[:space:]]' LogOS Tests | filter_demo_dirs | filter_whitelist)"
if [[ -n "${postulates}" ]]; then
  die $'found postulate outside whitelist:\n'"${postulates}"
fi

unsafe_opts="$(scan '--unsafe' LogOS Tests)"
if [[ -n "${unsafe_opts}" ]]; then
  die $'found --unsafe in OPTIONS pragma:\n'"${unsafe_opts}"
fi

unsolved_metas="$(scan '--allow-unsolved-metas' LogOS Tests)"
if [[ -n "${unsolved_metas}" ]]; then
  die $'found --allow-unsolved-metas in OPTIONS pragma:\n'"${unsolved_metas}"
fi

# Docs parity: scan Agda fenced code in literate docs too (no postulates/unsafe options).

docs_code="$(scan_docs_agda_blocks)"

docs_postulates="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:[[:space:]]*postulate([[:space:]]|$)' || true)"
if [[ -n "${docs_postulates}" ]]; then
  die $'found postulate in docs (Agda code blocks):\n'"${docs_postulates}"
fi

docs_unsafe_opts="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\\{-# OPTIONS[^}]*--unsafe' || true)"
if [[ -n "${docs_unsafe_opts}" ]]; then
  die $'found --unsafe in docs (Agda code blocks):\n'"${docs_unsafe_opts}"
fi

docs_unsolved_metas="$(printf "%s" "${docs_code}" | grep -E '^[^:]+:[0-9]+:.*\\{-# OPTIONS[^}]*--allow-unsolved-metas' || true)"
if [[ -n "${docs_unsolved_metas}" ]]; then
  die $'found --allow-unsolved-metas in docs (Agda code blocks):\n'"${docs_unsolved_metas}"
fi

echo "honesty-check: OK"
