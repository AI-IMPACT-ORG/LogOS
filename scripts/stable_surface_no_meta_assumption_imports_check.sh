#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-no-meta-assumption-imports-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "$ROOT"

# This check relies on ripgrep’s stable regex + glob semantics.
command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=lib/stable_packs.sh
source "${SCRIPT_DIR}/lib/stable_packs.sh"

# Policy: stable surfaces (API + stable pack Surface locks + core Surface entrypoints)
# must not import `LogOS.Theorems.Meta.Assumptions.*` directly.
#
# Rationale: stable “foundational” imports should not accidentally inherit
# meta-theorem assumptions (which are intentionally explicit and curated).
# Consumers should depend on curated stable packs / APIs instead.

files=(
  LogOS/Kernel/Surface.agda
  LogOS/Ports/Surface.agda
  LogOS/Adapters/Surface.agda
  LogOS/Theorems/Surface.agda
)

shopt -s nullglob
for f in LogOS/API/*.agda; do
  files+=("$f")
done
shopt -u nullglob

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
  if [[ ! -f "$file" ]]; then
    return 0
  fi

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

IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'
ASSUMPTION_IMPORT="${IMPORT_LINE}LogOS\\.Theorems\\.Meta\\.Assumptions\\."

for root in "${stable_roots[@]}"; do
  for f in "${root}/All.agda" "${root}/Core.agda" "${root}/Kernel.agda" "${root}/Surface.agda"; do
    [[ -f "${f}" ]] || continue
    files+=("${f}")
  done
done

for f in "${files[@]}"; do
  out="$(scan_file "$f" "${ASSUMPTION_IMPORT}")"
  if [[ -n "$out" ]]; then
    bad+="${out}"$'\n'
  fi
done

if [[ -n "$bad" ]]; then
  die $'found `LogOS.Theorems.Meta.Assumptions.*` imports in stable surfaces:\n'"${bad}"$'\n\nRule: stable surfaces must not import `LogOS.Theorems.Meta.Assumptions.*` directly.'
fi

echo "stable-surface-no-meta-assumption-imports-check: OK"
