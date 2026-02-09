#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "sketch-location-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# Policy:
# - Any “Sketch” content must live under a Demo/Demos directory.
#   This is enforced by name (basename contains Sketch) or by a Sketch directory segment.

find_candidates() {
  find . -type f \
    \( -name '*.agda' -o -name '*.lagda.md' \) \
    -not -path './_build/*' \
    \( -path '*/Sketch/*' -o -name '*Sketch*' -o -name '*sketch*' \)
}

is_under_demo_dir() {
  local path="$1"
  case "${path}" in
    *"/Demo/"*|*"/Demos/"*) return 0 ;;
    *) return 1 ;;
  esac
}

bad=""
while IFS= read -r f; do
  if ! is_under_demo_dir "${f}"; then
    bad+="${f}"$'\n'
  fi
done < <(find_candidates)

if [[ -n "${bad}" ]]; then
  die $'found Sketch files outside Demo/Demos folders:\n'"${bad}"
fi

echo "sketch-location-check: OK"
