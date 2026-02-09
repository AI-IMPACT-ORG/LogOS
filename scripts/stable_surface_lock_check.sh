#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-lock-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "$ROOT"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=lib/stable_packs.sh
source "${SCRIPT_DIR}/lib/stable_packs.sh"

# Policy: stable pack `Surface.agda` files should be “namespace locks”.
#
# Concretely:
# - Each stable pack surface must `open import LogOS.Packs.<Pack>.All public` at top-level.
# - Any additional imports must be inside a named submodule (i.e. indented deeper),
#   so they don't pollute the pack surface namespace and don't create accidental
#   name collisions across packs.
#
# This keeps `LogOS.Packs.*.Surface` safe to import as a stable, collision-resistant API.

stable_roots=()
stable_roots_text=""
if ! stable_roots_text="$(stable_pack_roots)"; then
  rc="$?"
  if [[ "$rc" -eq 1 ]]; then
    die "no stable packs found (expected `packTrust = record { level = stable }` in LogOS/Packs/**/All.agda)"
  fi
  die "failed to discover stable pack roots"
fi
while IFS= read -r root; do
  [[ -z "${root}" ]] && continue
  stable_roots+=("${root}")
done <<< "${stable_roots_text}"
if [ "${#stable_roots[@]}" -eq 0 ]; then
  die "no stable packs found (expected `packTrust = record { level = stable }` in LogOS/Packs/**/All.agda)"
fi

bad=""

for root in "${stable_roots[@]}"; do
  surface="${root}/Surface.agda"
  rel="${root#LogOS/Packs/}"
  packMod="${rel//\//.}"
  expected="open import LogOS.Packs.${packMod}.All public"

  if [[ ! -f "$surface" ]]; then
    bad+="${surface}: missing Surface.agda for stable pack root ${root}"$'\n'
    continue
  fi

  out=""
  awk_status=0
  set +e
  out="$(awk -v f="$surface" -v expected="$expected" '
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
          expLine = NR
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
    ' "$surface" 2>&1)"
  awk_status="$?"
  set -e

  if [[ "$awk_status" -eq 0 ]]; then
    if [[ -n "$out" ]]; then
      die $'internal error: surface lock awk produced output on success:\n'"${out}"
    fi
  elif [[ "$awk_status" -eq 1 ]]; then
    bad+="${out}"$'\n'
  else
    die $'internal error: surface lock awk failed:\n'"${out}"
  fi
done

if [[ -n "$bad" ]]; then
  die $'stable pack surface lock violations:\n'"${bad}"$'\n\nRule: stable `Surface.agda` should only open-import its own `All` at top-level; extra imports must be in a namespaced submodule.'
fi

echo "stable-surface-lock-check: OK"
