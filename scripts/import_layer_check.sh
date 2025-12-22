#!/usr/bin/env bash
# LogOS: an Agda Library for foundational logic architecture
# Copyright (C) 2025 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "import-layer-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

scan_in_dir() {
  local dir="$1"
  local pattern="$2"

  if [[ ! -d "$dir" ]]; then
    return 0
  fi

  if command -v rg >/dev/null 2>&1; then
    local out status
    set +e
    out="$(rg -n \
      --glob '*.agda' \
      --glob '!_build/**' \
      -- "${pattern}" "$dir" 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'rg error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  else
    local out status
    set +e
    out="$(grep -RIn --include='*.agda' --exclude-dir='_build' -E -- "${pattern}" "$dir" 2>&1)"
    status="$?"
    set -e
    if [[ "$status" -eq 2 ]]; then
      die $'grep error:\n'"${out}"
    fi
    if [[ "$status" -eq 1 ]]; then
      out=""
    fi
    printf "%s" "${out}"
  fi
}

check_no_imports() {
  local label="$1"
  local dir="$2"
  local pattern="$3"

  local out
  out="$(scan_in_dir "$dir" "$pattern")"
  if [[ -n "$out" ]]; then
    die $'layering violation ('"${label}"$'):\n'"${out}"
  fi
}

# Match only actual import lines to avoid comments/documentation.
IMPORT_LINE='^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]+'

# 1) Core layers must not depend on application layers or doc scaffolding.
CORE_FORBIDDEN="${IMPORT_LINE}LogOS\\.(Domain|Models|Packs|Docs)(\\.|$)"
CORE_DIRS=(
  LogOS/Base
  LogOS/Syntax
  LogOS/Minimal
  LogOS/Boundary
  LogOS/Algebra
  LogOS/Free
  LogOS/Kernel
  LogOS/Computation
  LogOS/Ports
  LogOS/Adapters
  LogOS/Theorems
  LogOS/API
)

for d in "${CORE_DIRS[@]}"; do
  check_no_imports "core must not import Domain/Models/Packs/Docs" "$d" "$CORE_FORBIDDEN"
done

# 2) Domain packs must not depend on curated surfaces or docs.
DOMAIN_FORBIDDEN="${IMPORT_LINE}LogOS\\.(Models|Packs|Docs)(\\.|$)"
check_no_imports "Domain must not import Models/Packs/Docs" "LogOS/Domain" "$DOMAIN_FORBIDDEN"

# 3) Curated surfaces must not depend on docs.
DOCS_FORBIDDEN="${IMPORT_LINE}LogOS\\.Docs(\\.|$)"
check_no_imports "Models must not import Docs" "LogOS/Models" "$DOCS_FORBIDDEN"
check_no_imports "Packs must not import Docs" "LogOS/Packs" "$DOCS_FORBIDDEN"

echo "import-layer-check: OK"

