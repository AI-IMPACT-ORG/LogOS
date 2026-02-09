#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-no-kernel-io-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "$ROOT"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=lib/stable_packs.sh
source "${SCRIPT_DIR}/lib/stable_packs.sh"

# Only match actual import lines to avoid prose references.
IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
FORBIDDEN="${IMPORT_LINE}LogOS\\.(Kernel(\\.|$)|Boundary\\.IO(\\.|$))"

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

bad=""

scan_file() {
  local file="$1"
  local pattern="$2"

  local out status
  set +e
  out="$(rg -n -- "${pattern}" "$file" 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    out=""
  fi
  printf "%s" "${out}"
}
for root in "${stable_roots[@]}"; do
  files=(
    "${root}/All.agda"
    "${root}/Core.agda"
    "${root}/Surface.agda"
  )

  for f in "${files[@]}"; do
    [[ -f "$f" ]] || continue

    hit="$(scan_file "$f" "${FORBIDDEN}")"

    if [[ -n "${hit}" ]]; then
      bad+="${hit}"$'\n'
    fi
  done
done

if [[ -n "${bad}" ]]; then
  die $'found forbidden direct imports in stable pack entrypoints:\n'"${bad}"$'\n\nUse the stable spines instead:\n- `LogOS.System` (open-system boundary view)\n- `LogOS.Ports.Semantic.*` / `LogOS.Adapters.*` (ports/adapters)\n- `LogOS.API.Kernel` (kernel-authoring only)'
fi

echo "stable-surface-no-kernel-io-imports-check: OK"
