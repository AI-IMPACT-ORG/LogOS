#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - All root-level Agda modules must be explicitly allowlisted.
# - Repo-root entries must stay within the maintained boundary contract.
# - Junk artifacts such as `__MACOSX`, `._*`, `.DS_Store`, `*.pyc`, and
#   `__pycache__` must not ship outside ignored build directories.

set -euo pipefail

CHECK_NAME="root-hygiene-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
ALLOWLIST_FILE="${SCRIPT_DIR}/root_hygiene_allowlist.txt"
ENTRY_ALLOWLIST_FILE="${SCRIPT_DIR}/root_entry_allowlist.txt"

cd "${LIB_ROOT}"

check_require_cmd "${CHECK_NAME}" rg

read_root_agda_allowlist() {
  local line
  while IFS= read -r line; do
    line="${line%%#*}"
    line="${line#"${line%%[![:space:]]*}"}"
    line="${line%"${line##*[![:space:]]}"}"
    [[ -z "${line}" ]] && continue
    [[ "${line}" == */* ]] && die "allowlist entry must be root-level: ${line}"
    [[ "${line}" == *.agda ]] || die "allowlist entry must be a .agda file: ${line}"
    printf "%s\n" "${line}"
  done < "${ALLOWLIST_FILE}"
}

read_root_entry_allowlist() {
  local line
  while IFS= read -r line; do
    line="${line%%#*}"
    line="${line#"${line%%[![:space:]]*}"}"
    line="${line%"${line##*[![:space:]]}"}"
    [[ -z "${line}" ]] && continue
    [[ "${line}" != */* ]] || die "root entry allowlist entry must be root-level: ${line}"
    printf "%s\n" "${line}"
  done < "${ENTRY_ALLOWLIST_FILE}"
}

collect_root_agda_files() {
  rg --files --glob '*.agda' --glob '!_build/**' | awk -F/ 'NF==1'
}

check_root_agda_files() {
  local -a roots=()
  local line
  local violations

  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    roots+=("${line}")
  done < <(collect_root_agda_files)

  (( ${#roots[@]} == 0 )) && return 0

  violations=""
  for line in "${roots[@]}"; do
    if ! printf '%s\n' "${allowed_root_files}" | rg -qx "${line}"; then
      violations+="\\n  - ${line}"
    fi
  done

  if [[ -n "${violations}" ]]; then
    die "root-level .agda files are only allowed if listed in scripts/root_hygiene_allowlist.txt:${violations}"
  fi
}

check_forbidden_root_notes() {
  if [[ -e "TEMP" ]]; then
    die "historical note file must not live at repo root: TEMP"
  fi

  if [[ -e "Archive.zip" ]]; then
    die "archive bundle must not live at repo root: Archive.zip"
  fi
}

check_root_entries() {
  local -a root_entries=()
  local line
  local entry_violations

  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    case "${line}" in
      .git|_build)
        continue
        ;;
    esac
    root_entries+=("${line}")
  done < <(find . -mindepth 1 -maxdepth 1 -exec basename {} \; | LC_ALL=C sort)

  entry_violations=""
  for line in "${root_entries[@]}"; do
    if ! printf '%s\n' "${allowed_root_entries}" | rg -qx "${line}"; then
      entry_violations+="\\n  - ${line}"
    fi
  done

  if [[ -n "${entry_violations}" ]]; then
    die "repo-root entries must stay within scripts/root_entry_allowlist.txt:${entry_violations}"
  fi
}

check_junk_artifacts() {
  local junk_hits
  local hit

  junk_hits=""
  while IFS= read -r hit; do
    [[ -z "${hit}" ]] && continue
    junk_hits+="\\n  - ${hit#./}"
  done < <(
    find . \
      \( -path './_build' -o -path './_build/*' \) -prune -o \
      \( -name '__MACOSX' -o -name '._*' -o -name '.DS_Store' -o -name '*.pyc' -o -name '__pycache__' \) \
      -print | LC_ALL=C sort
  )

  if [[ -n "${junk_hits}" ]]; then
    die "junk artifacts must not be present outside ignored build directories:${junk_hits}"
  fi
}

[[ -f "${ALLOWLIST_FILE}" ]] || die "missing allowlist file: ${ALLOWLIST_FILE}"
[[ -f "${ENTRY_ALLOWLIST_FILE}" ]] || die "missing root entry allowlist: ${ENTRY_ALLOWLIST_FILE}"

allowed_root_files="$(read_root_agda_allowlist)"
allowed_root_entries="$(read_root_entry_allowlist)"

# Always validate allowlist entries (even if there are no root .agda files).
unknown_allowlist=""
while IFS= read -r a; do
  [[ -z "${a}" ]] && continue
  if [[ ! -f "${a}" ]]; then
    unknown_allowlist+="\\n  - ${a}"
  fi
done <<< "${allowed_root_files}"

if [[ -n "${unknown_allowlist}" ]]; then
  die "allowlist entries that do not exist:${unknown_allowlist}"
fi

unknown_entry_allowlist=""
while IFS= read -r a; do
  [[ -z "${a}" ]] && continue
  if [[ ! -e "${a}" ]]; then
    unknown_entry_allowlist+="\\n  - ${a}"
  fi
done <<< "${allowed_root_entries}"

if [[ -n "${unknown_entry_allowlist}" ]]; then
  die "root entry allowlist entries that do not exist:${unknown_entry_allowlist}"
fi

check_root_agda_files
check_forbidden_root_notes
check_root_entries
check_junk_artifacts

echo "root-hygiene-check: OK"
