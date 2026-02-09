#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-no-experimental-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=lib/stable_packs.sh
source "${SCRIPT_DIR}/lib/stable_packs.sh"

stable_roots=()
stable_roots_text=""
if ! stable_roots_text="$(stable_pack_roots)"; then
  rc="$?"
  if [[ "$rc" -eq 1 ]]; then
    die "no stable packs found (expected `packTrust = record { level = stable }` in LogOS/Packs/**/All.agda)"
  fi
  die "failed to discover stable pack roots"
fi
while IFS= read -r root; do
  [[ -z "${root}" ]] && continue
  stable_roots+=("${root}")
done <<< "${stable_roots_text}"
if [ "${#stable_roots[@]}" -eq 0 ]; then
  die "no stable packs found (expected `packTrust = record { level = stable }` in LogOS/Packs/**/All.agda)"
fi

IMPORT_EXPERIMENTAL_PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+.*\.Experimental(\.|$)'

bad=""

for root in "${stable_roots[@]}"; do
  [[ -d "${root}" ]] || continue
  out=""
  status=0
  set +e
  out="$(rg -n \
    --glob '*.agda' \
    --glob '!**/_build/**' \
    --glob '!**/Experimental/**' \
    -- "${IMPORT_EXPERIMENTAL_PATTERN}" "${root}" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 0 ]]; then
    bad+="${out}"$'\n'
  fi
done

if [[ -n "${bad}" ]]; then
  die $'found Experimental imports in stable pack surfaces:\n'"${bad}"
fi

echo "stable-surface-no-experimental-imports-check: OK"
