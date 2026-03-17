#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `LogOS.API.Kernel` must expose the architecture / implementation / façade
#   split explicitly on the curated API surface.

set -euo pipefail

CHECK_NAME="architecture-api-surface-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

FILE="LogOS/API/Kernel.agda"
[[ -f "${FILE}" ]] || die "missing ${FILE}"

for pattern in \
  '^module Architecture where$' \
  '^module Implementation where$' \
  '^module Facade where$' \
  'open import LogOS\.LT\.LOG\.Boundary2Cat public' \
  'open import LogOS\.LT\.LOG\.Implementation2Cat public' \
  'open import LogOS\.LT\.LOG\.Kernel2Cat public' \
  'ltArchitectureImplementationLaw-ok'
do
  if ! rg -q -- "${pattern}" "${FILE}"; then
    die "${FILE}: missing expected architecture API surface pattern: ${pattern}"
  fi
done

echo "${CHECK_NAME}: OK"
