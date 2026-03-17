#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

# Small helper for policy scripts:
# extract Agda lines from fenced ```agda blocks.

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

# Prints all Agda code lines from fenced blocks under a given root.
docs_scan_agda_blocks() {
  # Defaults keep existing behavior: docs/*.lagda.md.
  local root="${1:-docs}"
  local pattern="${2:-*.lagda.md}"
  [[ -d "$root" ]] || return 0

  local tmp
  tmp="$(mktemp)"
  trap 'rm -f "$tmp"' RETURN

  # Avoid descending into generated artifacts.
  find "$root" \
    -type d -name '_build' -prune -o \
    -type f -name "$pattern" -print0 >"${tmp}"

  while IFS= read -r -d '' f; do
    docs_extract_agda_blocks "$f"
  done < "${tmp}"
}
