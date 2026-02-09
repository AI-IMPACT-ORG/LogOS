#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "topic-all-index-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Policy: topic-level `All.agda` modules are index-only (discoverability).
#
# Rationale: keep lightweight index modules stable and name-clash-minimal.
# Convenience re-exports belong in `Surface.agda` (or packs).

FILES=(
  LogOS/ZFC/All.agda
  LogOS/Universality/All.agda
  LogOS/UniversalIR/All.agda
  LogOS/Complexity/All.agda
  LogOS/ObjectLogic/All.agda
  LogOS/InfoTheory/All.agda
  LogOS/Domain/Opacity/All.agda
  LogOS/Domain/All.agda
)

PATTERN='^[[:space:]]*open[[:space:]]+import[[:space:]].*[[:space:]]+public([[:space:]]|$)'

bad=""
for f in "${FILES[@]}"; do
  [[ -f "${f}" ]] || continue
  hits="$(rg -n -- "${PATTERN}" "${f}" || true)"
  if [[ -n "${hits}" ]]; then
    bad+="${f}"$'\n'"${hits}"$'\n\n'
  fi
done

if [[ -n "${bad}" ]]; then
  die $'topic `All.agda` modules must not use `open import ... public` (use `Surface.agda`):\n\n'"${bad}"
fi

echo "topic-all-index-check: OK"

