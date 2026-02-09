#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "banned-imports-lint: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

# Policy: import host/builtin primitives only via LogOS.Prelude (or other dedicated shims).
#
# Rationale: the Prelude is the canonical “host contact surface”; direct imports of
# `Level`, propositional equality, and builtin units bypass this discipline.

PATTERN='^(open[[:space:]]+import|import)[[:space:]]+(Level|Data\\.Relation\\.Binary\\.PropositionalEquality|Agda\\.Builtin\\.Unit)([[:space:]]|$)'

# Small, explicit allowlist for foundational wrappers.
ALLOW_GLOBS=(
  '!LogOS/Prelude.agda'
  '!LogOS/Prelude/**'
  '!LogOS/API/Minimal.agda'
  '!LogOS/Kernel/Hom.agda'
  '!LogOS/Algebra/ConAlg.agda'
  '!LogOS/Minimal/Con.agda'
  '!LogOS/Minimal/Adapter.agda'
)

globs=(
  '*.agda'
  '!_build/**'
  '!.git/**'
  '!.agda/**'
)
globs+=("${ALLOW_GLOBS[@]}")

args=()
for g in "${globs[@]}"; do
  args+=(--glob "$g")
done

out=""
status=0
set +e
out="$(rg -n "${args[@]}" -- "${PATTERN}" LogOS Tests 2>&1)"
status="$?"
set -e
if [[ "$status" -eq 2 ]]; then
  die $'rg error:\n'"${out}"
fi
if [[ "$status" -eq 0 ]]; then
  die $'found banned direct imports (use LogOS.Prelude):\n'"${out}"
fi

docs_code="$(docs_scan_agda_blocks)"
docs_bad_imports="$(printf "%s" "${docs_code}" | grep -E "^[^:]+:[0-9]+:[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+(Level|Data\\.Relation\\.Binary\\.PropositionalEquality|Agda\\.Builtin\\.Unit)([[:space:]]|$)" || true)"
if [[ -n "${docs_bad_imports}" ]]; then
  die $'found banned direct imports in docs (Agda code blocks):\n'"${docs_bad_imports}"$'\n\nDocs should import host primitives via `LogOS.Prelude` as well.'
fi

echo "banned-imports-lint: OK"
