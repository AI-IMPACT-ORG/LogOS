#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "relation-symbol-governance-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
ALLOWLIST="${SCRIPT_DIR}/relation_symbol_governance_allowlist.txt"

cd "${LIB_ROOT}"

scan() {
  local pattern="$1"
  command -v rg >/dev/null 2>&1 || die "rg is required for this check"

  local out status
  set +e
  out="$(rg -n --glob '*.agda' --glob '!_build/**' --pcre2 -- "${pattern}" LogOS Tests Examples 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    out=""
  fi
  printf "%s" "${out}"
}

# Ban primitive record fields named `_≈_`.
#
# Rationale: `≈` is always mutual refinement, so record interfaces should expose
# a primitive preorder (`⊑`) and define `≈` as derived notation.
#
# This check is a small indentation-aware parser: it looks for `_≈_ : ...` lines
# that occur *inside* a `field` block.
check_no_field_approx() {
  local tmp
  tmp="$(mktemp)"

  roots=(LogOS)
  [[ -d Tests ]] && roots+=(Tests)
  [[ -d Examples ]] && roots+=(Examples)

  # We scan library code and its tests/examples; docs live elsewhere and are already typechecked.
  # The parser is intentionally conservative: it ignores blank lines and line
  # comments, and tracks field-block indentation.
  find "${roots[@]}" -type f -name '*.agda' -print0 |
    awk -v RS='\0' '
      function ltrim(s) { sub(/^[ \t]+/, "", s); return s }
      function indent_of(s,   m) { match(s, /^[ \t]*/); return RLENGTH }
      {
        file = $0
        in_field = 0
        field_indent = -1
        lineno = 0
        while ((getline line < file) > 0) {
          lineno++
          raw = line
          trimmed = ltrim(raw)

          # Ignore blank lines and line comments.
          if (trimmed == "" || trimmed ~ /^--/) { continue }

          ind = indent_of(raw)

          # Start of a field block.
          if (trimmed ~ /^field([[:space:]]|$)/) {
            in_field = 1
            field_indent = ind
            continue
          }

          # End of a field block (dedent).
          if (in_field && ind <= field_indent) {
            in_field = 0
            field_indent = -1
          }

          if (in_field && trimmed ~ /^_≈_[[:space:]]*:/) {
            printf "%s:%d:%s\n", file, lineno, raw
          }
        }
        close(file)
      }
    ' > "${tmp}"

  if [[ -s "${tmp}" ]]; then
    local out
    out="$(cat "${tmp}")"
    rm -f "${tmp}"
    die $'found primitive record fields named `_≈_` (define `⊑` as primitive and derive `≈`):\n'"${out}"
  fi

  rm -f "${tmp}"
}

# Relational governance: forbid introducing new relations named with `≈` that are
# definitional aliases for:
# - `≡` (should be `≃`), or
# - `≃` (still strict; should be named `≃`), or
# - `↔` / `ObsEqOn` (presentation; should be named `ObsEq…` and bridged to `≈`).
#
# We intentionally only target obvious definitional patterns:
# - `_≈..._ ... = ... ≡ ...`
# - `_≈..._ ... = ... ≃ ...`
# - `; _≈_ = _≡_` inside record instantiations
# - `; _≈_ = _≃_` inside record instantiations
# - infix operators that *start* with `≈`, e.g. `S ≈RunEq T = ... ≡ ...`
# - obvious `↔` / `ObsEqOn` aliases (same-line only; multi-line definitions are
#   intentionally not chased by this lightweight check)
#
# Existing violations are temporarily allowlisted while the codebase migrates
# to view-based naming (`≃[μ]` for strict equality; `≈[μ]` for mutual refinement).

hits=""

hits1="$(scan "^[[:space:]]*_[^=]*≈[^=]*=[^\\n]*≡")"
hits2="$(scan "^[[:space:]]*;[[:space:]]*_≈_[^=]*=[^\\n]*_≡_")"
hits3="$(scan "^[[:space:]]*[^[:space:]]+[[:space:]]+≈[^[:space:]]+[[:space:]]+[^=]+=[^\\n]*≡")"
hits4="$(scan "^[[:space:]]*_[^=]*≈[^=]*=[^\\n]*≃")"
hits5="$(scan "^[[:space:]]*;[[:space:]]*_≈_[^=]*=[^\\n]*_≃_")"
hits6="$(scan "^[[:space:]]*[^[:space:]]+[[:space:]]+≈[^[:space:]]+[[:space:]]+[^=]+=[^\\n]*≃")"
hits7="$(scan "^[[:space:]]*_[^=]*≈[^=]*=[^\\n]*↔")"
hits8="$(scan "^[[:space:]]*;[[:space:]]*_≈_[^=]*=[^\\n]*↔")"
hits9="$(scan "^[[:space:]]*[^[:space:]]+[[:space:]]+≈[^[:space:]]+[[:space:]]+[^=]+=[^\\n]*↔")"
hits10="$(scan "^[[:space:]]*_[^=]*≈[^=]*=[^\\n]*ObsEqOn")"
hits11="$(scan "^[[:space:]]*;[[:space:]]*_≈_[^=]*=[^\\n]*ObsEqOn")"
hits12="$(scan "^[[:space:]]*[^[:space:]]+[[:space:]]+≈[^[:space:]]+[[:space:]]+[^=]+=[^\\n]*ObsEqOn")"

if [[ -n "${hits1}" ]]; then hits+="${hits1}"$'\n'; fi
if [[ -n "${hits2}" ]]; then hits+="${hits2}"$'\n'; fi
if [[ -n "${hits3}" ]]; then hits+="${hits3}"$'\n'; fi
if [[ -n "${hits4}" ]]; then hits+="${hits4}"$'\n'; fi
if [[ -n "${hits5}" ]]; then hits+="${hits5}"$'\n'; fi
if [[ -n "${hits6}" ]]; then hits+="${hits6}"$'\n'; fi
if [[ -n "${hits7}" ]]; then hits+="${hits7}"$'\n'; fi
if [[ -n "${hits8}" ]]; then hits+="${hits8}"$'\n'; fi
if [[ -n "${hits9}" ]]; then hits+="${hits9}"$'\n'; fi
if [[ -n "${hits10}" ]]; then hits+="${hits10}"$'\n'; fi
if [[ -n "${hits11}" ]]; then hits+="${hits11}"$'\n'; fi
if [[ -n "${hits12}" ]]; then hits+="${hits12}"$'\n'; fi

# Normalize and drop empty lines.
hits="$(printf "%s" "${hits}" | sed '/^[[:space:]]*$/d' || true)"

if [[ -z "${hits}" ]]; then
  check_no_field_approx
  echo "relation-symbol-governance-check: OK"
  exit 0
fi

if [[ ! -f "${ALLOWLIST}" ]]; then
  die $'allowlist missing (expected scripts/relation_symbol_governance_allowlist.txt); hits:\n'"${hits}"
fi

remaining="$(printf "%s\n" "${hits}" | grep -v -F -f "${ALLOWLIST}" || true)"
if [[ -n "${remaining}" ]]; then
  die $'found ≈-named relations defined via ≡/≃/↔/ObsEqOn (use ≃ for strict, ObsEq… for ↔, or view-based ≈):\n'"${remaining}"
fi

check_no_field_approx

echo "relation-symbol-governance-check: OK (allowlisted hits present)"
