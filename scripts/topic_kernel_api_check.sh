#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "topic-kernel-api-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# Policy: topic libraries should treat the kernel as an API surface.
#
# Rationale: importing internal kernel modules (`LogOS.Kernel*`) directly makes
# kernel refactors expensive (high coupling). Topic libraries should import
# through `LogOS.API.Kernel` and wrapper modules under `LogOS.API.Kernel.*`.

PATTERN='^(open[[:space:]]+import|import)[[:space:]]+LogOS\\.Kernel(\\.|[[:space:]]|$)'

TOPIC_DIRS=(
  LogOS/ZFC
  LogOS/Universality
  LogOS/UniversalIR
  LogOS/Complexity
  LogOS/ObjectLogic
  LogOS/InfoTheory
)

out=""
status=0
set +e
out="$(rg -n --glob '*.agda' --glob '!_build/**' --glob '!.git/**' -- "${PATTERN}" "${TOPIC_DIRS[@]}" 2>&1)"
status="$?"
set -e

if [[ "$status" -eq 2 ]]; then
  die $'rg error:\n'"${out}"
fi

if [[ "$status" -eq 0 ]]; then
  die $'topic libraries must not import `LogOS.Kernel*` directly (use `LogOS.API.Kernel*`):\n'"${out}"
fi

echo "topic-kernel-api-check: OK"

