#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Documentation must name the meaning-injection / meaning-change compartments:
#   `LogOS/Ports/Quarantine/**` and `LogOS/Ports/Bridges/**`.
# - This prevents contributors from smuggling meaning changes into ordinary ports/adapters without noticing.

set -euo pipefail

CHECK_NAME="quarantine-story-doc-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

rg -q --fixed-strings "LogOS/Ports/Quarantine" docs/Patterns \
  || die "docs/Patterns must mention LogOS/Ports/Quarantine"

rg -q --fixed-strings "LogOS/Ports/Bridges" docs/Patterns \
  || die "docs/Patterns must mention LogOS/Ports/Bridges"

echo "${CHECK_NAME}: OK"
