#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="doc-import-discipline-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

# Policy: public-facing docs (docs/*.md outside docs/Core/Spec/**) should
# demonstrate the curated API surface rather than deep internal imports.

public_docs=()
while IFS= read -r f; do
  f="${f#./}"
  public_docs+=("${f}")
done < <(
  rg -l --glob '*.md' --glob '!docs/Core/Spec/**' '^[[:space:]]*```[[:space:]]*agda' docs
)

if ((${#public_docs[@]} == 0)); then
  echo "${CHECK_NAME}: OK (no public-facing markdown docs outside docs/Core/Spec/)"
  exit 0
fi

IMPORT_LINE='^[^:]+:[0-9]+:[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
NEED_API="${IMPORT_LINE}LogOS\\.API\\.LT([[:space:]]|$)"
FORBIDDEN_INTERNAL="${IMPORT_LINE}(Agda\\.|Agda\\.Builtin\\.|LogOS\\.(Prelude|Syntax|LT|Ports|Host)(\\.|$))"

missing_api=""
forbidden=""

for f in "${public_docs[@]}"; do
  [[ -f "${f}" ]] || continue

  code="$(docs_extract_agda_blocks "${f}" || true)"
  if [[ -z "${code}" ]]; then
    missing_api+="${f}: no fenced agda code blocks found"$'\n'
    continue
  fi

  if ! printf "%s" "${code}" | rg -q -- "${NEED_API}"; then
    missing_api+="${f}: missing import LogOS.API.LT in fenced Agda blocks"$'\n'
  fi

  hits="$(printf "%s" "${code}" | rg -- "${FORBIDDEN_INTERNAL}" || true)"
  if [[ -n "${hits}" ]]; then
    forbidden+="${hits}"$'\n'
  fi
done

errors=""
if [[ -n "${missing_api}" ]]; then
  errors+=$'missing required API import in public-facing docs:\n'"${missing_api}"$'\n'
fi
if [[ -n "${forbidden}" ]]; then
  errors+=$'found forbidden deep/internal imports in public-facing docs (Agda code blocks):\n'"${forbidden}"$'\n'
fi

if [[ -n "${errors}" ]]; then
  die $'\n'"${errors}"$'\nRule: docs outside docs/Core/Spec/** must import LogOS.API.LT (and avoid direct Prelude/Syntax/LT/Ports/Host imports).'
fi

echo "${CHECK_NAME}: OK"
