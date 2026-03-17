#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
#
# Policy:
# - Hard gate: forbid *local* `ConPreorder` constructions that collapse
#   refinement to equality (`_⊑_ = _≡_`) or that use a unit carrier as a boundary.
# - Canonical terminal/unit boundary is `LogOS.LT.ConPreorder.Unit`; canonical
#   equality-refinement boundary is `LogOS.LT.ConPreorder.Discrete`. This check
#   only applies to redefinitions outside those modules.
# - These can be useful for tiny scaffolds, but they are usually a smell in a
#   refinement-first codebase: they erase information and often hide where the
#   real observation/refinement structure should live.

set -euo pipefail

CHECK_NAME="trivial-boundary-smell-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

eq_hits="$(check_rg_capture "${CHECK_NAME}" -n -- ';[[:space:]]*_⊑_[[:space:]]*=[[:space:]]*_≡_' LogOS)"
unit_hits="$(check_rg_capture "${CHECK_NAME}" -n -- 'Con[[:space:]]*=[[:space:]]*⊤' LogOS)"

if [[ -n "${eq_hits}" ]]; then
  eq_hits="$(printf "%s\n" "${eq_hits}" | rg -v -F 'LogOS/LT/ConPreorder/Discrete.agda:' || true)"
fi

if [[ -n "${unit_hits}" ]]; then
  # Canonical terminal/unit boundary lives in LT; only report *local*
  # redefinitions that tend to hide the intended observation/refinement
  # structure in application/port code.
  unit_hits="$(printf "%s\n" "${unit_hits}" | rg -v -F 'LogOS/LT/ConPreorder/Unit.agda:' || true)"
fi

errors=""
if [[ -n "${eq_hits}" ]]; then
  errors+=$'found ConPreorder definitions using _⊑_ = _≡_ (refinement-collapse smell):\n'"${eq_hits}"$'\n'
fi

if [[ -n "${unit_hits}" ]]; then
  errors+=$'found ConPreorder definitions using Con = ⊤ (trivial-boundary smell):\n'"${unit_hits}"$'\n'
fi

if [[ -n "${errors}" ]]; then
  die $'\n'"${errors}"$'\nFix: import canonical boundaries from LogOS.LT.ConPreorder.Unit or LogOS.LT.ConPreorder.Discrete (or introduce a nontrivial boundary/refinement structure).'
fi

echo "${CHECK_NAME}: OK"
