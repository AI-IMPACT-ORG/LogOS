#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The enforced ports-as-displayed design note must explicitly document the closed loop:
#   canonical discipline gates + coverage check + API witnesses.

set -euo pipefail

CHECK_NAME="ports-as-displayed-doc-contract-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

DOC="docs/Patterns/Enforced_Ports_As_Displayed.lagda.md"
[[ -f "${DOC}" ]] || die "missing doc: ${DOC}"

require_token() {
  local tok="$1"
  if ! rg -q --fixed-strings "${tok}" "${DOC}"; then
    die "doc contract violation: missing '${tok}' in ${DOC}"
  fi
}

require_token "LogOS/LT/LOG/Discipline/PortsAsDisplayed.agda"
require_token "LogOS/LT/LOG/Discipline/StrictificationAsDisplayed.agda"
require_token "LogOS/Ports/Discipline/PortsAsDisplayed.agda"
require_token "scripts/check/ports_as_displayed_coverage_check.sh"
require_token "ltPortsAsDisplayed-ok"
require_token "ltStrictificationAsDisplayed-ok"
require_token "LogOS.Ports.Discipline.PortsAsDisplayed.ArchitectureLaws"

echo "${CHECK_NAME}: OK"
