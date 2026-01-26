#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "bad-code-smells-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

scan() {
  local pattern="$1"
  if command -v rg >/dev/null 2>&1; then
    local out status
    set +e
    out="$(rg -n --glob '*.agda' --glob '*.lagda.md' --glob '!_build/**' --pcre2 -- "${pattern}" . 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'rg error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  else
    local out status
    set +e
    out="$(grep -RIn --include='*.agda' --include='*.lagda.md' --exclude-dir='_build' -E -- "${pattern}" . 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'grep error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  fi
}

todo_hits="$(scan '\\b(TODO|FIXME|HACK|XXX)\\b')"
if [[ -n "${todo_hits}" ]]; then
  die $'found TODO/FIXME/HACK markers:\n'"${todo_hits}"
fi

stale_truthroute="$(scan 'LogOS\\.Domain\\.Complexity\\.TruthRoute\\b|LogOS/Domain/Complexity/TruthRoute\\.agda')"
if [[ -n "${stale_truthroute}" ]]; then
  die $'found stale TruthRoute references:\n'"${stale_truthroute}"
fi

stale_ibadapters="$(scan 'LogOS\\.Domain\\.Complexity\\.InfoBottleneckAdaptersGraded\\b|LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded\\.agda')"
if [[ -n "${stale_ibadapters}" ]]; then
  die $'found stale InfoBottleneckAdaptersGraded references:\n'"${stale_ibadapters}"
fi

pack_records="$(scan '^[[:space:]]*record[[:space:]]+Pack\\b')"
if [[ -n "${pack_records}" ]]; then
  pack_agda="$(printf '%s\n' "${pack_records}" | grep -v '\\.lagda\\.md:' || true)"
  pack_bad="$(printf '%s\n' "${pack_agda}" | grep -v '^LogOS/Theorems/Meta/QuartetCore\\.agda:' || true)"
  if [[ -n "${pack_bad}" ]]; then
    die $'found ad-hoc `record Pack` declarations (use QuartetCore instead):\n'"${pack_bad}"
  fi
fi

if [[ -f "LogOS/Domain/Complexity/TruthRoute.agda" ]]; then
  die "unexpected file exists: LogOS/Domain/Complexity/TruthRoute.agda"
fi

if [[ -f "LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded.agda" ]]; then
  die "unexpected file exists: LogOS/Domain/Complexity/InfoBottleneckAdaptersGraded.agda"
fi

echo "bad-code-smells-check: OK"
