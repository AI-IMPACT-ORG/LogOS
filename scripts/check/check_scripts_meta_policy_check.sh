#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Every `scripts/check/*_check.sh` must follow the standard check-script shape:
#   SPDX header, `set -euo pipefail`, `CHECK_NAME="..."`, and `scripts/lib/check_common.sh`.

set -euo pipefail

CHECK_NAME="check-scripts-meta-policy-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

missing_spdx=""
missing_seteuo=""
missing_check_name=""
missing_common_source=""

for f in scripts/check/*_check.sh; do
  [[ -f "${f}" ]] || continue

  if ! rg -q -- 'SPDX-License-Identifier:[[:space:]]*GPL-3\.0-only' "${f}"; then
    missing_spdx+="${f}"$'\n'
  fi

  if ! rg -q -- '^set -euo pipefail$' "${f}"; then
    missing_seteuo+="${f}"$'\n'
  fi

  if ! rg -q -- '^CHECK_NAME="[^"]+"$' "${f}"; then
    missing_check_name+="${f}"$'\n'
  fi

  if ! rg -q -- 'check_common\.sh' "${f}"; then
    missing_common_source+="${f}"$'\n'
  fi
done

errors=""
if [[ -n "${missing_spdx}" ]]; then
  errors+=$'missing SPDX header tag in check scripts:\n'"${missing_spdx}"$'\n'
fi
if [[ -n "${missing_seteuo}" ]]; then
  errors+=$'missing `set -euo pipefail` in check scripts:\n'"${missing_seteuo}"$'\n'
fi
if [[ -n "${missing_check_name}" ]]; then
  errors+=$'missing `CHECK_NAME=\"...\"` in check scripts:\n'"${missing_check_name}"$'\n'
fi
if [[ -n "${missing_common_source}" ]]; then
  errors+=$'missing `check_common.sh` source in check scripts:\n'"${missing_common_source}"$'\n'
fi

if [[ -n "${errors}" ]]; then
  die $'\n'"${errors}"
fi

echo "${CHECK_NAME}: OK"
