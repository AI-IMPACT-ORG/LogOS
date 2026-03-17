#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Forbid the `with-K` option in repository-level checked-in build/test configuration.

set -euo pipefail

CHECK_NAME="no-with-k-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

# A local override of K can still be injected from local CI commands or shell
# environments, and is blocked by the check scripts that consume `AGDA_FLAGS`.
# This policy enforces that no checked-in commands or snippets opt in to
# `--with-K`.
with_k_hits="$(rg -n --no-ignore --glob '!.git/**' --glob '!_build/**' --glob '!.agda/**' --glob '!scripts/check/no_with_k_check.sh' --glob '!scripts/lib/check_common.sh' -- '--with-K' . || true)"

if [[ -n "${with_k_hits}" ]]; then
  die $'found forbidden --with-K usage:\n'"${with_k_hits}"
fi

echo "${CHECK_NAME}: OK"
