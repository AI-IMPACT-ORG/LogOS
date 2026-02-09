#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "kernel-antisymmetry-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Enforce explicit intent for antisymmetry usage in the kernel.
#
# Policy: the kernel is preorder-first; partial-order/antisymmetry structure is
# an explicit strengthening that must remain quarantined to a small, auditable
# set of modules.
ANTISYM_PATTERN='(BulkBoundaryPO|PartialOrder|po-bnd|antisym)'
ALLOWLIST_FILE="scripts/kernel_antisymmetry_allowlist.txt"

read_allowlist() {
  if [[ ! -f "${ALLOWLIST_FILE}" ]]; then
    die "missing allowlist file: ${ALLOWLIST_FILE}"
  fi

  invalid=""
  while IFS= read -r raw; do
    line="${raw%%$'\r'}"
    trimmed="${line#"${line%%[![:space:]]*}"}"
    [[ -z "${trimmed}" ]] && continue
    [[ "${trimmed}" == \#* ]] && continue

    main="${line%%#*}"
    main="${main%"${main##*[![:space:]]}"}"
    main="${main#"${main%%[![:space:]]*}"}"
    comment="${line#*#}"

    if [[ "${line}" != *"#"* ]] || [[ "${comment}" != *"JUSTIFICATION:"* ]]; then
      invalid+="${raw}"$'\n'
      continue
    fi

    [[ -n "${main}" ]] || { invalid+="${raw}"$'\n'; continue; }

    if [[ ! -f "${main}" ]]; then
      invalid+="${raw}  (missing file: ${main})"$'\n'
      continue
    fi

    printf "%s\n" "${main#./}"
  done < "${ALLOWLIST_FILE}"

  if [[ -n "${invalid}" ]]; then
    die $'invalid allowlist entries (each entry must be `path  # JUSTIFICATION: ...`):\n'"${invalid}"
  fi
}

scan_kernel() {
  local out status
  set +e
  out="$(rg -n --glob 'LogOS/Kernel/**/*.agda' --glob '!**/_build/**' -- "${ANTISYM_PATTERN}" . 2>&1)"
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

hits="$(scan_kernel)"
if [[ -n "${hits}" ]]; then
  hits="$(printf "%s" "${hits}" | grep -v -E '^[^:]+:[0-9]+:[[:space:]]*--' || true)"
  while IFS= read -r allowed; do
    [[ -z "${allowed}" ]] && continue
    hits="$(printf "%s" "${hits}" | grep -v -F "${allowed}:" || true)"
    hits="$(printf "%s" "${hits}" | grep -v -F "./${allowed}:" || true)"
  done < <(read_allowlist)
fi

if [[ -n "${hits}" ]]; then
  die $'found kernel antisymmetry usage outside the allowlist:\n'"${hits}"$'\n\nAllowed files are listed in: '"${ALLOWLIST_FILE}"
fi

echo "kernel-antisymmetry-check: OK"
