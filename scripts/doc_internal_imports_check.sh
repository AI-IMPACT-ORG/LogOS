#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "doc-internal-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

cd "${LIB_ROOT}"

# Policy: publication-facing docs should demonstrate stable import surfaces.
#
# We treat `docs/Applications/*.lagda.md` as “publication-facing”, and forbid
# deep internal imports in Agda code blocks:
#   - `LogOS.Domain.*`
#   - `LogOS.Theorems.*`
#   - `LogOS.Kernel.*`
#   - `LogOS.Ports.*`
#   - `LogOS.Adapters.*`
#
# Prefer `LogOS.API.*` and `LogOS.Packs.*` surfaces instead.

DOCS_ROOTS=()
if [[ "${#}" -ge 1 ]]; then
  DOCS_ROOTS+=("${1}")
else
  DOCS_ROOTS+=("docs/Applications" "docs/Views")
fi

IMPORT_LINE='^[^:]+:[0-9]+:[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
FORBIDDEN="${IMPORT_LINE}LogOS\\.(Domain|Theorems|Kernel|Ports|Adapters)(\\.|$)"

hits=""
for root in "${DOCS_ROOTS[@]}"; do
  [[ -d "${root}" ]] || continue
  hits+=$(docs_scan_agda_blocks "${root}" | grep -E -- "${FORBIDDEN}" || true)
  hits+=$'\n'
done

if [[ -n "${hits//[[:space:]]/}" ]]; then
  die $'found forbidden deep internal imports in docs (Agda code blocks):\n'"${hits}"$'\n\nPrefer `LogOS.API.*` / `LogOS.Packs.*` surfaces.'
fi

echo "doc-internal-imports-check: OK"
