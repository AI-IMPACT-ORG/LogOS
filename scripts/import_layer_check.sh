#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "import-layer-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v rg >/dev/null 2>&1 || die "rg is required for this check"

scan_in_dir() {
  local dir="$1"
  local pattern="$2"

  if [[ ! -e "$dir" ]]; then
    return 0
  fi

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

# 1) Core layers must not depend on application layers or documentation scaffolding.
# Object-level logic developments are also treated as non-core.
CORE_FORBIDDEN="${IMPORT_LINE}(LogOS\\.(Domain|Packs|ObjectLogic)(\\.|$)|docs(\\.|$))"
CORE_DIRS=(
  LogOS/Axioms
  LogOS/Base
  LogOS/Syntax
  LogOS/Minimal
  LogOS/Boundary
  LogOS/Algebra
  LogOS/Free
  LogOS/Kernel
  LogOS/QAdapters
  LogOS/Computation
  LogOS/MetaLanguage
  LogOS/Ports
  LogOS/Adapters
  LogOS/System.agda
  LogOS/Theorems
  LogOS/API
)

for d in "${CORE_DIRS[@]}"; do
  check_no_imports "core must not import Domain/Packs/ObjectLogic/docs" "$d" "$CORE_FORBIDDEN"
done

# 1b) Topic libraries (mature) must not depend on Packs/Domain/docs.
#
# Rationale: these libraries are intended to be safe transitive dependencies of
# stable pack surfaces.
TOPIC_FORBIDDEN="${IMPORT_LINE}(LogOS\\.(Domain|Packs)(\\.|$)|docs(\\.|$))"
TOPIC_DIRS=(
  LogOS/ZFC
  LogOS/UniversalIR
  LogOS/Universality
  LogOS/Complexity
  LogOS/InfoTheory
  LogOS/ObjectLogic
)
for d in "${TOPIC_DIRS[@]}"; do
  check_no_imports "topics must not import Domain/Packs/docs" "$d" "$TOPIC_FORBIDDEN"
done

# 2) Domain packs must not depend on curated pack surfaces or docs.
DOMAIN_FORBIDDEN="${IMPORT_LINE}(LogOS\\.Packs(\\.|$)|docs(\\.|$))"
check_no_imports "Domain must not import Packs/docs" "LogOS/Domain" "$DOMAIN_FORBIDDEN"

# 3) Curated pack surfaces must not depend on docs.
DOCS_FORBIDDEN="${IMPORT_LINE}docs(\\.|$)"
check_no_imports "Packs must not import docs" "LogOS/Packs" "$DOCS_FORBIDDEN"

echo "import-layer-check: OK"
