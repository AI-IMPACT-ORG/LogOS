#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

# Canonical layer order for `LogOS/**`.
#
# Lower rank = lower layer (more foundational).
# Policy rule: higher layers may import lower layers; lower layers may not
# import higher layers.
LAYERS=(
  Host
  Prelude
  Syntax
  LT
  Ports
  Adapters
  Apps
  API
  Checks
)

layer_rank() {
  local layer="$1"
  local i=0
  for item in "${LAYERS[@]}"; do
    if [[ "${item}" == "${layer}" ]]; then
      printf '%s\n' "${i}"
      return 0
    fi
    i=$((i + 1))
  done
  return 1
}

layers_csv() {
  local IFS=,
  printf '%s\n' "${LAYERS[*]}"
}
