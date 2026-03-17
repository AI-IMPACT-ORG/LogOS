#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `docs/Patterns/All.lagda.md` is the curated entrypoint for design notes.
# - Every `docs/Patterns/*.lagda.md` note (except the index itself) must be referenced from the index.

set -euo pipefail

CHECK_NAME="design-index-coverage-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

INDEX="docs/Patterns/All.lagda.md"
[[ -f "${INDEX}" ]] || die "missing design index: ${INDEX}"

missing=""
while IFS= read -r f; do
  [[ -n "${f}" ]] || continue
  [[ "${f}" == "${INDEX}" ]] && continue

  if ! rg -q --fixed-strings "${f}" "${INDEX}"; then
    missing+="${f}"$'\n'
  fi
done < <(find docs/Patterns -maxdepth 1 -type f -name '*.lagda.md' | LC_ALL=C sort)

if [[ -n "${missing}" ]]; then
  die $'docs/Patterns/All.lagda.md is missing references to design notes:\n'"${missing}"$'\nRule: every docs/Patterns/*.lagda.md file (except the index itself) must be linked from the design index.'
fi

echo "${CHECK_NAME}: OK"
