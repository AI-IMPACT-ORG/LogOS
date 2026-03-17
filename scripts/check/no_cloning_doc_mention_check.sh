#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The Deutsch no-cloning sidecar must be discoverable from documentation (not only from code).

set -euo pipefail

CHECK_NAME="no-cloning-doc-mention-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

rg -q --fixed-strings "LogOS/Ports/AbstractDeutschNoCloning.agda" docs \
  || die "missing doc mention: LogOS/Ports/AbstractDeutschNoCloning.agda"

echo "${CHECK_NAME}: OK"

