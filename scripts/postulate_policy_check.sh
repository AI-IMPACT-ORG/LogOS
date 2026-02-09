#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "postulate-policy-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
ALLOWLIST_FILE="${SCRIPT_DIR}/postulate_allowlist.txt"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

scan() {
  local pattern="$1"

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
}

read_allowlist() {
  if [[ ! -f "${ALLOWLIST_FILE}" ]]; then
    die "missing allowlist file: ${ALLOWLIST_FILE}"
  fi

  local line
  while IFS= read -r line; do
    line="${line%%#*}"
    line="${line#"${line%%[![:space:]]*}"}"
    line="${line%"${line##*[![:space:]]}"}"
    [[ -z "${line}" ]] && continue
    printf "%s\n" "${line#./}"
  done < "${ALLOWLIST_FILE}"
}

filter_allowlist() {
  local out
  out="$(cat)"
  local f
  while IFS= read -r f; do
    [[ -z "${f}" ]] && continue
    out="$(printf "%s" "${out}" | grep -v -F "${f}:" || true)"
    out="$(printf "%s" "${out}" | grep -v -F "./${f}:" || true)"
  done < <(read_allowlist)
  printf "%s" "${out}"
}

justification_ok() {
  local file="$1"
  local missing=()

  grep -q "POSTULATE-JUSTIFICATION" "$file" || missing+=("POSTULATE-JUSTIFICATION")
  grep -q -E "Threat model:" "$file" || missing+=("Threat model:")
  grep -q -E "Why unavoidable:" "$file" || missing+=("Why unavoidable:")
  grep -q -E "Isolation:" "$file" || missing+=("Isolation:")
  grep -q -E "Forbidden imports:" "$file" || missing+=("Forbidden imports:")

  if ((${#missing[@]})); then
    printf "missing justification fields (%s)\n" "${missing[*]}"
    return 1
  fi
  return 0
}

POSTULATE_PATTERN='^[[:space:]]*postulate[[:space:]]*$|^[[:space:]]*postulate[[:space:]]'
postulates="$(scan "${POSTULATE_PATTERN}" | filter_allowlist)"
if [[ -n "${postulates}" ]]; then
  die $'found postulate outside explicit allowlist:\n'"${postulates}"$'\n\nRule: `postulate` is forbidden by default; whitelist specific files in scripts/postulate_allowlist.txt.'
fi

# For whitelisted files that contain `postulate`, require a structured justification.
postulate_files=""
out=""
status=0
set +e
out="$(rg -l --glob '*.agda' --glob '!_build/**' -- "${POSTULATE_PATTERN}" . 2>&1)"
status="$?"
set -e
if [[ "$status" -eq 2 ]]; then
  die $'rg error:\n'"${out}"
fi
if [[ "$status" -eq 1 ]]; then
  out=""
fi
postulate_files="$(printf "%s" "${out}" | sed 's#^\\./##')"

if [[ -n "${postulate_files}" ]]; then
  while IFS= read -r f; do
    [[ -z "${f}" ]] && continue
    f="${f#./}"
    # Enforce that every postulate-bearing file is explicitly whitelisted.
    if ! read_allowlist | grep -Fxq "${f}"; then
      die "file contains 'postulate' but is not in allowlist: ${f}"
    fi
    if ! reason="$(justification_ok "${f}")"; then
      die "file contains 'postulate' but lacks required justification block: ${f} (${reason})"
    fi
  done <<< "${postulate_files}"
fi

# Docs parity: do not allow `postulate` in Agda fenced code blocks.

docs_postulates="$(docs_scan_agda_blocks | grep -E '^[^:]+:[0-9]+:[[:space:]]*postulate([[:space:]]|$)' || true)"
if [[ -n "${docs_postulates}" ]]; then
  die $'found postulate in docs (Agda code blocks):\n'"${docs_postulates}"
fi

echo "postulate-policy-check: OK"
