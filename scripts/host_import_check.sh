#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "host-import-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

# This check relies on ripgrep’s stable regex + glob semantics.
command -v rg >/dev/null 2>&1 || die "rg is required for this check"

# shellcheck source=scripts/lib/docs_agda_blocks.sh
source "${SCRIPT_DIR}/lib/docs_agda_blocks.sh"

# Policy:
# - `LogOS/Host/**` is the host-wrapper layer.
# - Everywhere else should access host shims via `LogOS.Prelude(.agda|/**)`.
#   This makes host contact points structurally trivial to audit.

filter_allowed() {
  local out
  out="$(cat)"

  # Allow direct `LogOS.Host.*` imports inside the host wrapper layer itself.
  out="$(printf "%s" "$out" | grep -v -F "LogOS/Host/" || true)"

  # Allow the curated Prelude surface to be the host re-export bridge.
  out="$(printf "%s" "$out" | grep -v -F "LogOS/Prelude.agda:" || true)"
  out="$(printf "%s" "$out" | grep -v -F "LogOS/Prelude/" || true)"

  printf "%s" "$out"
}

scan_imports() {
  local pattern="$1"

  local out status
  set +e
  out="$(rg -n --glob '*.agda' --glob '!_build/**' -- "${pattern}" . 2>&1)"
  status="$?"
  set -e
  if [[ "$status" -eq 2 ]]; then
    die $'rg error:\n'"${out}"
  fi
  if [[ "$status" -eq 1 ]]; then
    out=""
  fi
  printf "%s" "${out}"
}

HOST_IMPORT_PATTERN='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+LogOS\\.Host\\.'

bad_imports="$(scan_imports "${HOST_IMPORT_PATTERN}" | filter_allowed)"
if [[ -n "${bad_imports}" ]]; then
  die $'found direct `LogOS.Host.*` imports outside the Prelude bridge:\n'"${bad_imports}"$'\n\n'"Allowed locations: LogOS/Host/** and LogOS/Prelude(.agda|/**)."
fi

# Docs parity: forbid direct Host imports inside docs/*.lagda.md Agda code blocks.
docs_bad_imports="$(docs_scan_agda_blocks | grep -E '^[^:]+:[0-9]+:[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+LogOS\\.Host\\.' || true)"
if [[ -n "${docs_bad_imports}" ]]; then
  die $'found direct `LogOS.Host.*` imports in docs (Agda code blocks):\n'"${docs_bad_imports}"$'\n\nDocs should import `LogOS.Prelude` / API surfaces, not Host shims directly.'
fi

echo "host-import-check: OK"
