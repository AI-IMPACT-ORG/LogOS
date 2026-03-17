#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The ports-as-displayed design note must document the canonical constructors, so contributors
#   copy the normal form rather than inventing bespoke encodings.

set -euo pipefail

CHECK_NAME="ports-as-displayed-design-contract-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

DOC="docs/Patterns/Ports_As_Displayed.lagda.md"
[[ -f "${DOC}" ]] || die "missing doc: ${DOC}"

require_token() {
  local tok="$1"
  if ! rg -q --fixed-strings "${tok}" "${DOC}"; then
    die "doc contract violation: missing '${tok}' in ${DOC}"
  fi
}

require_token "DisplayedThin2Cat"
require_token "DecoratedThin2Cat"
require_token "forgetDecorated"
require_token "ProductDisplayed"

echo "${CHECK_NAME}: OK"
