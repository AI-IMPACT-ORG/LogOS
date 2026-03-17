#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Curated strictification modules should advertise one explicit strict object,
#   the downgrade path back to refinement, and a named law/anchor.

set -euo pipefail

CHECK_NAME="strictification-contract-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(".").resolve()
MANIFEST = ROOT / "scripts" / "strictification_contract_manifest.tsv"


def module_to_path(module_name: str) -> Path:
    return ROOT / (module_name.replace(".", "/") + ".agda")


if not MANIFEST.is_file():
    print("strictification-contract-check: FAIL", file=sys.stderr)
    print(f"  - missing manifest {MANIFEST.relative_to(ROOT).as_posix()}", file=sys.stderr)
    raise SystemExit(1)

violations: list[str] = []

for i, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    cols = raw.split("\t")
    if len(cols) != 5:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: expected 5 tab-separated columns", file=sys.stderr)
        raise SystemExit(1)
    module_name, strict_symbol, approx_symbol, under_symbol, law_symbol = [col.strip() for col in cols]
    path = module_to_path(module_name)
    if not path.is_file():
        violations.append(f"missing strictification module: {module_name}")
        continue
    text = path.read_text(encoding="utf-8")
    for label, symbol in (
        ("strict object", strict_symbol),
        ("approx downgrade", approx_symbol),
        ("under downgrade", under_symbol),
        ("law/anchor", law_symbol),
    ):
        if symbol == "-":
            continue
        if symbol not in text:
            violations.append(f"{path.relative_to(ROOT).as_posix()}: missing {label} symbol {symbol}")

if violations:
    print("strictification-contract-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("strictification-contract-check: OK")
PY
