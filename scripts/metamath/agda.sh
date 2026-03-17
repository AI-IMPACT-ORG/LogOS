#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd -- "${SCRIPT_DIR}/../../" && pwd)"

AGDA_BIN="${AGDA_BIN:-${AGDA:-agda}}"

AGDA_PEDANTIC_FLAGS=(
  --no-libraries
  -W
  all
  -W
  error
  -i
  "${REPO_ROOT}"
  -i
  "${REPO_ROOT}/_build/metamath"
)

exec "${AGDA_BIN}" "${AGDA_PEDANTIC_FLAGS[@]}" "$@"
