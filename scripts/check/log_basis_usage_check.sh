#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - LOG-basis port categories may not be imported from internal LT/Ports code by default.
#   Use LOGᴳ-basis categories internally, and allow LOG imports only for explicit physics/Deutsch
#   allowlisted modules.

set -euo pipefail

CHECK_NAME="log-basis-usage-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(".").resolve()

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")

LOG_BASIS_MODULES = (
    "LogOS.LT.LOG.Flow2Cat",
    "LogOS.LT.LOG.Contract2Cat",
    "LogOS.LT.LOG.EncodePort2Cat",
    "LogOS.LT.LOG.QuotePort2Cat",
)

ALLOWED_PREFIXES = (
    "LogOS/Ports/AbstractDeutsch2Cat/",
    "LogOS/Ports/AbstractDeutsch2Cat.agda",
    "LogOS/Ports/AbstractDeutschNoCloning.agda",
    "LogOS/Ports/Causality.agda",
    "LogOS/Ports/Universality/FlowBudget2Cat.agda",
    "LogOS/Ports/Universality/ArchitectureFlowBudget2Cat.agda",
    "LogOS/Ports/Discipline/PortsAsDisplayed/Core.agda",
)


def is_log_basis_import(dep: str) -> bool:
    return any(dep == mod or dep.startswith(mod + ".") for mod in LOG_BASIS_MODULES)


def allowed_importer(rel: str) -> bool:
    return any(rel.startswith(p) or rel == p for p in ALLOWED_PREFIXES)


def scan_dir(path: Path) -> list[str]:
    violations: list[str] = []
    for agda in sorted(path.rglob("*.agda")):
        if "_build" in agda.parts:
            continue

        rel = agda.relative_to(ROOT).as_posix()

        # LOG-basis modules are defined under LogOS/LT/LOG/**; skip them.
        if rel.startswith("LogOS/LT/LOG/"):
            continue

        if allowed_importer(rel):
            continue

        for i, line in enumerate(agda.read_text(encoding="utf-8").splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            dep = m.group(1)
            if is_log_basis_import(dep):
                violations.append(f"{rel}:{i}: forbidden LOG-basis import: {dep}")

    return violations


def main() -> int:
    violations: list[str] = []

    lt_dir = ROOT / "LogOS" / "LT"
    ports_dir = ROOT / "LogOS" / "Ports"

    if lt_dir.is_dir():
        violations += scan_dir(lt_dir)
    if ports_dir.is_dir():
        violations += scan_dir(ports_dir)

    if violations:
        print("log-basis-usage-check: FAIL", file=sys.stderr)
        print(
            "Policy: internal LT/Ports modules must use LOGᴳ-basis categories by default.",
            file=sys.stderr,
        )
        print(
            "LOG-basis imports are only allowed in explicitly allowlisted physics/Deutsch modules.",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    print("log-basis-usage-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
