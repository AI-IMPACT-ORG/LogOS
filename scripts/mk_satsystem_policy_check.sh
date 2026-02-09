#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

# Policy: `mkSatSystem` is the low-level constructor for SatSystem.
#
# To keep the “ports/adapters spine” easy to audit, we require all call sites
# (code and docs) to use the canonical wrapper `satSystem` instead.
#
# The only allowed occurrence of `mkSatSystem` is its definition site:
#   - LogOS/Ports/Semantic/PresentationCore.agda

RG_PATTERN='\\bmkSatSystem\\b'

command -v rg >/dev/null 2>&1 || { echo "mk-satsystem-policy-check: rg is required for this check" >&2; exit 1; }

dirs=(LogOS)
[[ -d Tests ]] && dirs+=(Tests)
[[ -d docs ]] && dirs+=(docs)

out=""
status=0
set +e
out="$(rg -n \
  --glob '!**/_build/**' \
  --glob '!LogOS/Ports/Semantic/PresentationCore.agda' \
  -- "${RG_PATTERN}" "${dirs[@]}" 2>&1)"
status="$?"
set -e
if [[ "$status" -eq 2 ]]; then
  echo "mk-satsystem-policy-check: rg error:" >&2
  echo "$out" >&2
  exit 1
fi
if [[ "$status" -eq 1 ]]; then
  out=""
fi

if [[ -n "$out" ]]; then
  echo "mk-satsystem-policy-check: forbidden mkSatSystem usages found." >&2
  echo "Use satSystem (LogOS.Ports.Semantic.PresentationCore.satSystem, re-exported by LogOS.Ports.Semantic.Core)." >&2
  echo >&2
  echo "$out" >&2
  exit 1
fi

echo "mk-satsystem-policy-check: OK"
