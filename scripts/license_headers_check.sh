#!/usr/bin/env bash
set -euo pipefail

# LogOS: an Agda Library for foundational logic architecture
# Copyright (C) 2025 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

die() {
  echo "license-headers-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

TITLE_LINE="LogOS: an Agda Library for foundational logic architecture"
COPY_LINE="Copyright (C) 2025 AI.IMPACT GmbH"
SPDX_LINE="SPDX-License-Identifier: GPL-3.0-only"

scan_files() {
  find . \
    -type f \
    \( \
      -name '*.agda' -o -name '*.md' -o -name '*.lagda.md' -o \
      -name '*.sh' -o -name '*.yml' -o -name '*.yaml' -o -name '*.cff' -o \
      -name 'Makefile' -o -name '.gitignore' \
    \) \
    -not -path './_build/*' \
    -not -path './.git/*' \
    -not -path './.agda/*' \
    -not -path './LICENSE' \
    -not -path './LogOS.agda-lib' \
    -print0
}

bad=""
while IFS= read -r -d '' f; do
  head="$(sed -n '1,40p' "$f")"
  echo "$head" | grep -Fq "$TITLE_LINE" || bad+="${f}: missing title header"$'\n'
  echo "$head" | grep -Fq "$COPY_LINE" || bad+="${f}: missing copyright header"$'\n'
  echo "$head" | grep -Fq "$SPDX_LINE" || bad+="${f}: missing SPDX identifier"$'\n'
done < <(scan_files)

if [[ -n "$bad" ]]; then
  die $'missing required per-file license header:\n'"${bad}"
fi

echo "license-headers-check: OK"

