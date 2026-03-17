#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"
# shellcheck source=scripts/lib/layers.sh
source "${SCRIPT_DIR}/lib/layers.sh"

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

OUT_PATH="${1:-docs/Generated/Architecture_Layer_Order.md}"
OUT_DIR="$(dirname "${OUT_PATH}")"
mkdir -p "${OUT_DIR}"

tmp="$(mktemp)"
trap 'rm -f "${tmp}"' EXIT

{
  cat <<'DOC'
<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Layer Order (Generated)

This file is generated from `scripts/lib/layers.sh` by `scripts/gen/write_layer_order_legend.sh`.

Policy rule: higher layers may import lower layers; lower layers may not import higher layers.

Layers (low -> high):
DOC

  i=0
  for layer in "${LAYERS[@]}"; do
    printf "%d. \`%s\` (rank %d)\n" "$((i + 1))" "${layer}" "${i}"
    i=$((i + 1))
  done
} > "${tmp}"

mv "${tmp}" "${OUT_PATH}"
echo "write-layer-order-legend: wrote ${OUT_PATH}"
