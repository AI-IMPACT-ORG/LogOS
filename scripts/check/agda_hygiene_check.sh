#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Enforce import/open hygiene across LogOS/*.agda.
# - `open import` must use `using`/`hiding`/`renaming`, except for curated public re-exports.
# - `open import ... public` is allowed in `LogOS/API/**`, `LogOS/Prelude.agda`,
#   and thin façade modules that publicly re-export their sibling `Core` module.
# - `open` (non-import) is allowed without `using`/`hiding`/`renaming` (record/module opens are routinely total);
#   prefer explicit lists when opening large namespaces.
# - Forbid anonymous `module _` at the top level.
# - Forbid Agda files over AGDA_HYGIENE_LINE_LIMIT lines (default 700).
# - Forbid duplicate basenames within a namespace branch (top-level + optional
#   two-level prefix + basename), e.g. `Apps/ZFC/Core`. This catches real
#   accidental collisions while allowing intentional domain-specific naming.
# - This is a hard policy check in `ci-policy`; there are no opt-out skip flags.

set -euo pipefail

CHECK_NAME="agda-hygiene-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg
check_require_cmd "${CHECK_NAME}" find
check_require_cmd "${CHECK_NAME}" wc
check_require_cmd "${CHECK_NAME}" awk
check_require_cmd "${CHECK_NAME}" sort

LOGOS_DIR="LogOS"
LINE_LIMIT="${AGDA_HYGIENE_LINE_LIMIT:-700}"
if [[ ! "${LINE_LIMIT}" =~ ^[0-9]+$ ]]; then
  die "AGDA_HYGIENE_LINE_LIMIT must be a non-negative integer"
fi

PUBLIC_REEXPORT_PREFIXES=("LogOS/API/"
"LogOS/Host/")
PUBLIC_REEXPORT_FILES=("LogOS/Prelude.agda")

UNQUALIFIED_OPEN_IMPORT_MODULES=("LogOS.Prelude")

imported_module_from_line() {
  local line="$1"
  local module=""
  read -r _open _import module _rest <<< "${line}"
  printf '%s' "${module}"
}

expected_core_module_for_path() {
  local path="$1"
  local core_file="${path%.agda}/Core.agda"
  [[ -f "${core_file}" ]] || return 1
  local module="${path%.agda}"
  module="${module//\//.}"
  printf '%s.Core' "${module}"
}

is_public_reexport_allowed() {
  local path="$1"
  local line="${2:-}"
  path="${path#./}"
  local prefix
  for prefix in "${PUBLIC_REEXPORT_PREFIXES[@]}"; do
    if [[ "${path}" == "${prefix}"* ]]; then
      return 0
    fi
  done
  local file
  for file in "${PUBLIC_REEXPORT_FILES[@]}"; do
    if [[ "${path}" == "${file}" ]]; then
      return 0
    fi
  done
  if [[ -n "${line}" ]]; then
    local expected_core=""
    if expected_core="$(expected_core_module_for_path "${path}")"; then
      local imported_module=""
      imported_module="$(imported_module_from_line "${line}")"
      if [[ "${imported_module}" == "${expected_core}" ]]; then
        return 0
      fi
    fi
  fi
  return 1
}

has_qualifying_using_hiding_renaming() {
  local line="$1"
  if [[ "${line}" =~ [[:space:]]renaming([[:space:]]|$) ]]; then
    return 0
  fi
  if [[ "${line}" =~ [[:space:]]using([[:space:]]|$) ]] \
    && ! [[ "${line}" =~ [[:space:]]using[[:space:]]*\([[:space:]]*\) ]]; then
    return 0
  fi
  if [[ "${line}" =~ [[:space:]]hiding([[:space:]]|$) ]] \
    && ! [[ "${line}" =~ [[:space:]]hiding[[:space:]]*\([[:space:]]*\) ]]; then
    return 0
  fi
  return 1
}

has_public() {
  local line="$1"
  [[ "${line}" =~ (^|[[:space:]])public([[:space:]]|$) ]]
}

is_unqualified_open_import_allowed() {
  local line="$1"
  local module=""
  read -r _open _import module _rest <<< "${line}"
  if [[ -z "${module}" ]]; then
    return 1
  fi
  local allowed
  for allowed in "${UNQUALIFIED_OPEN_IMPORT_MODULES[@]}"; do
    if [[ "${module}" == "${allowed}" ]]; then
      return 0
    fi
  done
  return 1
}

append_line() {
  local var="$1"
  local line="$2"
  if [[ -z "${!var}" ]]; then
    printf -v "${var}" "%s" "${line}"
  else
    printf -v "${var}" "%s\n%s" "${!var}" "${line}"
  fi
}

viol_unqualified_open_import=""
viol_public_reexport=""
open_imports="$(check_rg_capture "${CHECK_NAME}" -n -g '*.agda' -P '^\s*open\s+import\s+' "${LOGOS_DIR}")"
if [[ -n "${open_imports}" ]]; then
  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    file="${line%%:*}"
    rest="${line#*:}"
    lineno="${rest%%:*}"
    content="${rest#*:}"
    file="${file#./}"

    if has_public "${content}"; then
      if ! is_public_reexport_allowed "${file}" "${content}"; then
        append_line viol_public_reexport "${file}:${lineno}: ${content}"
      fi
    fi

    if ! has_qualifying_using_hiding_renaming "${content}" \
      && ! has_public "${content}" \
      && ! is_unqualified_open_import_allowed "${content}"; then
      append_line viol_unqualified_open_import "${file}:${lineno}: ${content}"
    fi
  done <<< "${open_imports}"
fi

viol_module_underscore=""
module_underscore="$(check_rg_capture "${CHECK_NAME}" -n -g '*.agda' -P '^\s*module\s+_\b' "${LOGOS_DIR}")"
if [[ -n "${module_underscore}" ]]; then
  while IFS= read -r line; do
    [[ -z "${line}" ]] && continue
    append_line viol_module_underscore "${line}"
  done <<< "${module_underscore}"
fi

viol_large_files=""
while IFS= read -r -d '' path; do
  [[ "${path}" == *"/_build/"* ]] && continue
  count="$(wc -l < "${path}")"
  if (( count > LINE_LIMIT )); then
    append_line viol_large_files "${path}: ${count} lines"
  fi
done < <(find "${LOGOS_DIR}" -type f -name '*.agda' -print0)

viol_duplicate_basenames=""
dup_report="$(
  find "${LOGOS_DIR}" -type f -name '*.agda' -print \
    | awk -F/ '
      {
        rel=$0
        sub(/^\.\/LogOS\//, "", rel)
        sub(/^LogOS\//, "", rel)
        n=split(rel, parts, "/")
        base=parts[n]
        if (n >= 4) {
          namespace=parts[1] "/" parts[2] "/" parts[3]
        } else if (n >= 3) {
          namespace=parts[1] "/" parts[2]
        } else {
          namespace=parts[1]
        }
        key=namespace "/" base
        by_key[key] = by_key[key] "\n    " $0
        count[key]++
      }
      END {
        for (k in count) {
          if (count[k] > 1) {
            print k ":" by_key[k] "\n"
          }
        }
      }' \
    | sort
)"
if [[ -n "${dup_report}" ]]; then
  viol_duplicate_basenames="${dup_report}"
fi

report=""
if [[ -n "${viol_public_reexport}" ]]; then
  report+=$'Public re-exports outside LogOS/API/** or LogOS/Prelude.agda:\n'
  report+="${viol_public_reexport}"$'\n\n'
fi
if [[ -n "${viol_unqualified_open_import}" ]]; then
  report+=$'Unqualified open import (missing using/hiding/renaming):\n'
  report+="${viol_unqualified_open_import}"$'\n\n'
fi
if [[ -n "${viol_module_underscore}" ]]; then
  report+=$'Anonymous module `_` declarations:\n'
  report+="${viol_module_underscore}"$'\n\n'
fi
if [[ -n "${viol_large_files}" ]]; then
  report+=$"Agda files over ${LINE_LIMIT} lines:\n"
  report+="${viol_large_files}"$'\n\n'
fi
if [[ -n "${viol_duplicate_basenames}" ]]; then
  report+=$'Duplicate Agda basenames:\n'
  report+="${viol_duplicate_basenames}"$'\n'
fi

if [[ -n "${report}" ]]; then
  echo "${CHECK_NAME}: FAIL" >&2
  echo "Agda hygiene violations:" >&2
  echo "${report}" >&2
  exit 1
fi

echo "${CHECK_NAME}: OK"
