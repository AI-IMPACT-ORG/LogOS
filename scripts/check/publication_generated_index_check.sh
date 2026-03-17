#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The generated publication index must stay in sync with the explicit
#   publication manifest and allowlists.

set -euo pipefail

CHECK_NAME="publication-generated-index-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" cmp

tmpdir="$(mktemp -d)"
trap 'rm -rf "${tmpdir}"' EXIT

target="docs/Generated/Published_Surface_Index.md"
tmp_out="${tmpdir}/Published_Surface_Index.md"

[[ -f "${target}" ]] || die "missing generated doc: ${target}"

bash scripts/gen/write_published_surface_index.sh "${tmp_out}" >/dev/null

if ! cmp -s "${target}" "${tmp_out}"; then
  die $'generated publication index is stale:\n  docs/Generated/Published_Surface_Index.md (run: make published-surface-index)'
fi

echo "${CHECK_NAME}: OK"
