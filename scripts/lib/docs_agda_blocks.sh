#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

# Small helper for policy scripts:
# extract Agda lines from fenced ```agda blocks inside literate docs (*.lagda.md).

docs_extract_agda_blocks() {
  # Prints Agda code lines inside ```agda fenced blocks, prefixed with file:line:.
  local file="$1"
  awk -v f="$file" '
    BEGIN { inside = 0 }
    /^[[:space:]]*```[[:space:]]*agda[[:space:]]*$/ { inside = 1; next }
    /^[[:space:]]*```[[:space:]]*$/ { if (inside == 1) { inside = 0; next } }
    inside == 1 { printf "%s:%d:%s\n", f, NR, $0 }
  ' "$file"
}

docs_scan_agda_blocks() {
  # Prints all Agda code lines inside docs/*.lagda.md fenced blocks.
  local root="${1:-docs}"
  [[ -d "$root" ]] || return 0

  local tmp
  tmp="$(mktemp)"
  trap 'rm -f "$tmp"' RETURN

  # Avoid descending into generated artifacts.
  find "$root" \
    -type d -name '_build' -prune -o \
    -type f -name '*.lagda.md' -print0 >"${tmp}"

  while IFS= read -r -d '' f; do
    docs_extract_agda_blocks "$f"
  done < "${tmp}"
}
