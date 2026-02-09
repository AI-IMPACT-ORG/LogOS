#!/usr/bin/env bash
set -euo pipefail

# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

# Canonical per-file header lines.
HEADER_TITLE_LINE="LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI"
HEADER_COPY_LINE="Copyright (C) 2026 AI.IMPACT GmbH"
HEADER_SPDX_LINE="SPDX-License-Identifier: GPL-3.0-only"

# Legacy title lines we may still find in old frontmatter.
HEADER_LEGACY_TITLE_LINES=(
  "LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning"
)

# Explicit allowlist for files expected to carry the per-file license frontmatter.
HEADER_ALLOW_GLOBS=(
  "*.agda"
  "*.lagda.md"
  "*.md"
  "*.sh"
  "*.py"
  "*.txt"
  "*.yml"
  "*.yaml"
  "*.tex"
  "*.bib"
  "*.cff"
  "*.agda-lib"
  "Makefile"
  ".gitignore"
)

# Exclusions for generated/build/cache folders.
HEADER_EXCLUDE_GLOBS=(
  ".git/**"
  "_build/**"
  ".agda/**"
)

header_list_allowlisted_files() {
  local -a cmd
  local g
  cmd=(rg --files --hidden --no-ignore)
  for g in "${HEADER_EXCLUDE_GLOBS[@]}"; do
    cmd+=(-g "!${g}")
  done
  for g in "${HEADER_ALLOW_GLOBS[@]}"; do
    cmd+=(-g "${g}")
  done
  "${cmd[@]}"
}
