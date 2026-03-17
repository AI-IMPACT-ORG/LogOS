#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Port totalisations must be explicit and discoverable: do not define new `= DecoratedThin2Cat ...`
#   outside `*2Cat.agda` modules (except discipline gates).
# - This prevents bypassing coverage/enforcement by hiding port categories in other files.

set -euo pipefail

CHECK_NAME="no-hidden-decoratedthin2cat-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

hits="$(check_rg_capture "${CHECK_NAME}" -l -g'*.agda' '=\\s*DecoratedThin2Cat\\b' LogOS/LT/LOG LogOS/Ports)"

violations=""
while IFS= read -r f; do
  [[ -z "${f}" ]] && continue

  if [[ "${f}" == *2Cat.agda ]]; then
    continue
  fi
  if [[ "${f}" == */Discipline/* ]]; then
    continue
  fi

  violations+="${f}"$'\n'
done <<< "${hits}"

if [[ -n "${violations}" ]]; then
  die $'hidden `= DecoratedThin2Cat ...` definitions (must live in `*2Cat.agda` or a discipline gate):\n'"${violations}"
fi

echo "${CHECK_NAME}: OK"
