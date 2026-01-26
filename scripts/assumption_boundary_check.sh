#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

fail=0

if command -v rg >/dev/null 2>&1; then
  if rg -n "FlowAssumptions|JClosureAssumptions" LogOS >/dev/null 2>&1; then
    echo "Assumption boundary lint: legacy closure-assumption names found."
    rg -n "FlowAssumptions|JClosureAssumptions" LogOS
    fail=1
  fi

  if rg -n "record[[:space:]]+.*Assumptions" LogOS/Kernel LogOS/Boundary LogOS/Ports >/dev/null 2>&1; then
    echo "Assumption boundary lint: Assumptions records must live outside core layers."
    rg -n "record[[:space:]]+.*Assumptions" LogOS/Kernel LogOS/Boundary LogOS/Ports
    fail=1
  fi
else
  out="$(grep -RInE "FlowAssumptions|JClosureAssumptions" LogOS 2>/dev/null || true)"
  if [ -n "$out" ]; then
    echo "Assumption boundary lint: legacy closure-assumption names found."
    printf '%s\n' "$out"
    fail=1
  fi

  out2="$(grep -RInE "record[[:space:]]+.*Assumptions" LogOS/Kernel LogOS/Boundary LogOS/Ports 2>/dev/null || true)"
  if [ -n "$out2" ]; then
    echo "Assumption boundary lint: Assumptions records must live outside core layers."
    printf '%s\n' "$out2"
    fail=1
  fi
fi

if [ "$fail" -ne 0 ]; then
  exit 1
fi

echo "Assumption boundary lint OK."
