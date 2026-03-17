#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - A small set of documentation capstones are part of the audited surface and must exist.

set -euo pipefail

CHECK_NAME="required-docs-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

required=(
  "docs/Patterns/Ports_As_Displayed.lagda.md"
  "docs/Patterns/Enforced_Ports_As_Displayed.lagda.md"
  "docs/Core/Textbook/Sections/S03_Displayed_Structure.lagda.md"
)

missing=""
for f in "${required[@]}"; do
  [[ -f "${f}" ]] || missing+="${f}"$'\n'
done

if [[ -n "${missing}" ]]; then
  die $'missing required docs:\n'"${missing}"
fi

echo "${CHECK_NAME}: OK"
