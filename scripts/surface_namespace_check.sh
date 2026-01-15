#!/usr/bin/env bash
# LogOS: an Agda research library for foundational logic system architecture.
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "surface-namespace-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

status=0

while IFS= read -r -d '' surf; do
  parent="$(basename "$(dirname "${surf}")")"
  if [[ "${parent}" == "Experimental" ]]; then
    pack="$(basename "$(dirname "$(dirname "${surf}")")")"
    allowed="open import LogOS.Packs.${pack}.Experimental.All public"
  else
    pack="${parent}"
    allowed="open import LogOS.Packs.${pack}.All public"
  fi

  # Top-level imports start at column 1; nested module imports are indented.
  top_imports="$(grep -n '^open import ' "${surf}" || true)"

  if [[ -z "${top_imports}" ]]; then
    echo "surface-namespace-check: ${surf}: missing top-level \`${allowed}\`" >&2
    status=1
    continue
  fi

  missing_allowed="$(printf '%s\n' "${top_imports}" | grep -F "${allowed}" || true)"
  if [[ -z "${missing_allowed}" ]]; then
    echo "surface-namespace-check: ${surf}: missing required \`${allowed}\`" >&2
    status=1
  fi

  bad="$(printf '%s\n' "${top_imports}" | grep -v -F "${allowed}" || true)"
  if [[ -n "${bad}" ]]; then
    echo "surface-namespace-check: ${surf}: unexpected top-level open imports:" >&2
    echo "${bad}" >&2
    status=1
  fi
done < <(find LogOS/Packs -mindepth 2 -maxdepth 3 -type f -name 'Surface.agda' -print0)

if [[ "${status}" -ne 0 ]]; then
  exit 1
fi

echo "surface-namespace-check: OK"
