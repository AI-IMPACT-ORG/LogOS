#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Every `scripts/check/*_check.sh` must be runnable as a `make <check-name>` target and be wired into `make ci-policy`,
#   unless explicitly allowlisted with a justification.

set -euo pipefail

CHECK_NAME="policy-coverage-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

ALLOWLIST_FILE="${SCRIPT_DIR}/policy_coverage_allowlist.txt"
[[ -f "${ALLOWLIST_FILE}" ]] || die "missing allowlist: ${ALLOWLIST_FILE}"
[[ -f "Makefile" ]] || die "missing Makefile"

read_allowlist() {
  local line
  while IFS= read -r line; do
    line="${line%%#*}"
    line="${line#"${line%%[![:space:]]*}"}"
    line="${line%"${line##*[![:space:]]}"}"
    [[ -z "${line}" ]] && continue
    printf '%s\n' "${line}"
  done < "${ALLOWLIST_FILE}"
}

contains() {
  local needle="$1"
  shift
  local item
  for item in "$@"; do
    [[ "${item}" == "${needle}" ]] && return 0
  done
  return 1
}

all_scripts=()
while IFS= read -r script; do
  [[ -z "${script}" ]] && continue
  all_scripts+=("${script}")
done < <(find scripts/check -maxdepth 1 -type f -name '*_check.sh' -exec basename {} \; | sort -u)

allowlisted=()
while IFS= read -r script; do
  [[ -z "${script}" ]] && continue
  allowlisted+=("${script}")
done < <(read_allowlist)

invalid_allowlist=""
if ((${#allowlisted[@]})); then
  for script in "${allowlisted[@]}"; do
    if ! contains "${script}" "${all_scripts[@]}"; then
      invalid_allowlist+="${script} (not found under scripts/check/*_check.sh)"$'\n'
    fi
  done
fi
[[ -z "${invalid_allowlist}" ]] || die $'invalid allowlist entries:\n'"${invalid_allowlist}"

ci_line="$(rg '^ci-policy:' Makefile | head -n 1 || true)"
[[ -n "${ci_line}" ]] || die "missing ci-policy target in Makefile"

deps_text="${ci_line#ci-policy:}"
read -r -a ci_deps <<< "${deps_text}"

missing=""
for script in "${all_scripts[@]}"; do
  if ((${#allowlisted[@]})) && contains "${script}" "${allowlisted[@]}"; then
    continue
  fi

  target="${script%.sh}"
  target="${target//_/-}"

  if ! rg -q -- "^${target}:" Makefile; then
    missing+="${script}: missing Makefile target '${target}'"$'\n'
    continue
  fi

  if ! rg -q -- "scripts/check/${script}" Makefile; then
    missing+="${script}: Makefile does not invoke scripts/check/${script}"$'\n'
    continue
  fi

  if ! contains "${target}" "${ci_deps[@]}"; then
    missing+="${script}: '${target}' is not wired into 'ci-policy'"$'\n'
  fi
done

if [[ -n "${missing}" ]]; then
  die $'policy coverage violations:\n'"${missing}"$'\n\nFix: add the target to `ci-policy` in Makefile, or justify it in scripts/policy_coverage_allowlist.txt.'
fi

echo "${CHECK_NAME}: OK"
