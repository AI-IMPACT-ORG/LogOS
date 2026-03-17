#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="agda-policy-bundle-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

# Policy: bundle the overlapping Agda surface policy checks into one fast pass.
#
# This check replaces the individual python-based scanners that used to live in:
# - bridge-contract-check
# - bridges-no-public-reexport-check
# - no-proj12-displayed-check
# - ports-bridges-import-check
# - ports-funpreorder-usage-check
# - globalise-import-check
# - refinement-reasoning-usage-check
# - theorems-no-eq-check
# - conpreorder-open-check
#
# Rationale:
# - these checks share the same Agda comment-stripping and file-scanning machinery,
# - bundling reduces duplicated code and CI overhead,
# - policies remain separate in the error report (one section per sub-check).

python3 -B scripts/lib/agda_policy_bundle.py "$@"
