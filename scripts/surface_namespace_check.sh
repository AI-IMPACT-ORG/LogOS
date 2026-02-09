#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "surface-namespace-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

status=0

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

find LogOS/Packs \
  -type d -name '_build' -prune -o \
  -type f -name 'Surface.agda' -print0 >"${tmp}"

count=0
while IFS= read -r -d '' surf; do
  count=$((count + 1))
  surf="${surf#./}"

  rel="${surf#LogOS/Packs/}"
  rel_dir="$(dirname "${rel}")"
  pack_mod="${rel_dir//\//.}"
  allowed="open import LogOS.Packs.${pack_mod}.All public"

  out=""
  awk_status=0
  set +e
  out="$(awk -v f="$surf" -v expected="$allowed" '
      function ind(s) { match(s, /^[ ]*/); return RLENGTH }
      /^[ ]*(open[ ]+import|import)[ ]+/ {
        n++
        line[n] = $0
        lineno[n] = NR
        trim = $0
        sub(/^[ ]+/, "", trim)
        trimmed[n] = trim
        indent[n] = ind($0)
        if (trim == expected) {
          if (base != "") dup = 1
          base = indent[n]
        }
      }
      END {
        bad = 0
        if (dup) {
          printf "%s: multiple required surface imports: %s\n", f, expected
          bad = 1
        }
        if (base == "") {
          printf "%s: missing required surface import: %s\n", f, expected
          bad = 1
        }
        if (base != "" && base != 0) {
          printf "%s:%d: required surface import must be top-level (no indentation): %s\n", f, expLine, expected
          bad = 1
        }
        for (i = 1; i <= n; i++) {
          if (trimmed[i] == expected) continue
          if (base != "" && indent[i] <= base) {
            printf "%s:%d: top-level surface import must be namespaced (wrap in `module ... where`): %s\n", f, lineno[i], trimmed[i]
            bad = 1
          }
        }
        exit bad
      }
    ' "$surf" 2>&1)"
  awk_status="$?"
  set -e

  if [[ "$awk_status" -eq 0 ]]; then
    if [[ -n "$out" ]]; then
      die $'internal error: surface lock awk produced output on success:\n'"${out}"
    fi
  elif [[ "$awk_status" -eq 1 ]]; then
    echo "$out" >&2
    status=1
  else
    die $'internal error: surface lock awk failed:\n'"${out}"
  fi
done < "${tmp}"

if [[ "${count}" -eq 0 ]]; then
  die "no pack Surface.agda files found under LogOS/Packs"
fi

if [[ "${status}" -ne 0 ]]; then
  exit 1
fi

echo "surface-namespace-check: OK"
