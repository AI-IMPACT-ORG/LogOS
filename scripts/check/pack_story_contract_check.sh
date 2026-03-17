#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Each application pack (`LogOS/Apps/*`) must declare its public story in `LogOS/Apps/*/All.agda`:
#   `Entrypoints:`, `Implemented now:`, and `Planned:`.
#
# Rationale:
# - Avoid scattered `README.md` files: pack story lives next to the pack's
#   curated entrypoint module.

set -euo pipefail

CHECK_NAME="pack-story-contract-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" rg

packs=()
while IFS= read -r d; do
  [[ -n "${d}" ]] || continue
  packs+=("${d}")
done < <(find LogOS/Apps -mindepth 1 -maxdepth 1 -type d | sort -u)

if ((${#packs[@]} == 0)); then
  die "no application pack directories found under LogOS/Apps/*"
fi

bad=""
for d in "${packs[@]}"; do
  story="${d}/All.agda"
  if [[ ! -f "${story}" ]]; then
    bad+="${story}: missing required pack entrypoint (expected for every LogOS/Apps/* pack)"$'\n'
    continue
  fi
  missing=()

  rg -q --fixed-strings "Entrypoints:" "${story}" || missing+=("Entrypoints:")
  rg -q --fixed-strings "Implemented now:" "${story}" || missing+=("Implemented now:")
  rg -q --fixed-strings "Planned:" "${story}" || missing+=("Planned:")

  if ((${#missing[@]})); then
    bad+="${story}: missing required sections: ${missing[*]}"$'\n'
  fi
done

if [[ -n "${bad}" ]]; then
  die $'pack story contract violations:\n'"${bad}"$'\n\nRule: each LogOS/Apps/* pack entrypoint (`All.agda`) must include:\n- Entrypoints:\n- Implemented now:\n- Planned:'
fi

echo "${CHECK_NAME}: OK"
