#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

# This check relies on ripgrep’s stable regex + glob semantics.
command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Docs/paper describe the repository as `--safe` by default. Enforce that every
# Agda module and literate Agda module opts into `--safe`.

SAFE_PRAGMA_LINE='{-# OPTIONS --safe #-}'

missing=""

list_files() {
  local glob="$1"
  rg --files --hidden \
    --glob "${glob}" \
    --glob '!_build/**' \
    --glob '!.git/**' \
    --glob '!.agda/**'
}

check_agda_safe() {
  local file="$1"
  awk -v f="$file" -v pragma="${SAFE_PRAGMA_LINE}" '
    BEGIN { safe = 0; mod = 0; ln = 0; bad = 0 }
    {
      ln++
      line = $0
      sub(/^[[:space:]]+/, "", line)
      sub(/[[:space:]]+$/, "", line)
      if (safe == 0 && line == pragma) { safe = ln }
      if (line ~ /^\{-# OPTIONS/ && line != pragma) {
        printf "%s:%d: forbidden OPTIONS pragma (only `%s` is allowed): %s\n", f, ln, pragma, line
        bad = 1
      }
      if (mod == 0 && line ~ /^module[[:space:]]+[A-Za-z0-9_.]+/) { mod = ln }
    }
    END {
      if (bad) exit 6
      if (safe == 0) exit 3
      if (mod == 0) exit 4
      if (safe > mod) exit 5
      exit 0
    }
  ' "$file"
}

# For *.lagda.md: require that the first ```agda block contains the pragma,
# that it appears before the module header in that block, and that no other
# OPTIONS pragmas occur anywhere in fenced Agda blocks.
check_lagda_safe() {
  local file="$1"
  awk -v f="$file" -v pragma="${SAFE_PRAGMA_LINE}" '
    BEGIN { inside = 0; seen_any = 0; block = 0; safe = 0; mod = 0; blockLine = 0; bad = 0 }
    /^[[:space:]]*```[[:space:]]*agda[[:space:]]*$/ {
      inside = 1;
      seen_any = 1;
      block++;
      if (block == 1) { blockLine = 0 }
      next
    }
    /^[[:space:]]*```[[:space:]]*$/ {
      if (inside == 1) { inside = 0 }
      next
    }
    inside == 1 {
      if (block == 1) blockLine++
      line = $0
      sub(/^[[:space:]]+/, "", line)
      sub(/[[:space:]]+$/, "", line)
      if (line ~ /^\{-# OPTIONS/ && line != pragma) {
        printf "%s:%d: forbidden OPTIONS pragma in fenced Agda block (only `%s` is allowed): %s\n", f, NR, pragma, line
        bad = 1
      }
      if (block == 1) {
        if (safe == 0 && line == pragma) { safe = blockLine }
        if (mod == 0 && line ~ /^module[[:space:]]+[A-Za-z0-9_.]+/) { mod = blockLine }
      }
    }
    END {
      if (bad) exit 6
      if (seen_any == 0) exit 2
      if (safe == 0) exit 3
      if (mod == 0) exit 4
      if (safe > mod) exit 5
      exit 0
    }
  ' "$file"
}

while IFS= read -r f; do
  [[ -z "$f" ]] && continue
  out=""
  if ! out="$(check_agda_safe "$f")"; then
    code="$?"
    case "$code" in
      3) missing+="${f#./}: missing \`${SAFE_PRAGMA_LINE}\`"$'\n' ;;
      4) missing+="${f#./}: missing module header"$'\n' ;;
      5) missing+="${f#./}: safe pragma must appear before module header"$'\n' ;;
      6) missing+="${out}"$'\n' ;;
      *) missing+="${f#./}: invalid safe pragma placement"$'\n' ;;
    esac
  fi
done < <(list_files '*.agda')

while IFS= read -r f; do
  [[ -z "$f" ]] && continue
  out=""
  if ! out="$(check_lagda_safe "$f")"; then
    code="$?"
    case "$code" in
      2) missing+="${f#./}: missing fenced agda block marker"$'\n' ;;
      3) missing+="${f#./}: missing '${SAFE_PRAGMA_LINE}' in first fenced agda block"$'\n' ;;
      4) missing+="${f#./}: missing module header in first fenced agda block"$'\n' ;;
      5) missing+="${f#./}: safe pragma must appear before module header in first fenced agda block"$'\n' ;;
      6) missing+="${out}"$'\n' ;;
      *) missing+="${f#./}: invalid safe pragma placement"$'\n' ;;
    esac
  fi
done < <(list_files '*.lagda.md')

if [[ -n "${missing}" ]]; then
  die $'missing/invalid `{-# OPTIONS --safe #-}` pragma:\n'"${missing}"$'\n\nFor docs (*.lagda.md), the pragma must appear inside the first ```agda block, before the module header.'
fi

echo "safe-options-check: OK"
