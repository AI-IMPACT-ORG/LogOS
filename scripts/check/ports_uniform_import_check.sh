#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="ports-uniform-import-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

forbidden_files=(
  "LogOS/API/Ports/Uniform.agda"
  "LogOS/Ports/Locality/Uniform.agda"
  "LogOS/Ports/PhysicalTransformers/Uniform.agda"
  "LogOS/Ports/BoundaryAsCode/Uniform.agda"
)

violations=""
for file in "${forbidden_files[@]}"; do
  if [[ -e "${file}" ]]; then
    violations+="module file still exists: ${file}"$'\n'
  fi
done

pattern='^[[:space:]]*((open[[:space:]]+import|import)[[:space:]]+LogOS\.(API\.Ports|Ports\.(Locality|PhysicalTransformers|BoundaryAsCode))\.Uniform\b|module[[:space:]]+[^=[:space:]]+[[:space:]]*=[[:space:]]*LogOS\.(API\.Ports|Ports\.(Locality|PhysicalTransformers|BoundaryAsCode))\.Uniform\b)'

matches="$(rg -n --glob='LogOS/**/*.agda' "${pattern}" LogOS || true)"
if [[ -n "${matches}" ]]; then
  violations+="${matches}"$'\n'
fi

if [[ -n "${violations}" ]]; then
  die $'uniform wrapper residue detected (uniform modules/imports must not exist):\n'"${violations}"
fi

echo "${CHECK_NAME}: OK"
