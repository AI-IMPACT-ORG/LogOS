#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Every canonical `*2Cat.agda` port totalisation must be typechecked through the
#   corresponding canonical discipline gate.
# - Explicit strictification ports are covered by a separate strictification gate.

set -euo pipefail

CHECK_NAME="ports-as-displayed-coverage-check"
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


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    if not rel.endswith(".agda"):
        raise ValueError(f"expected .agda file: {rel}")
    return rel[: -len(".agda")].replace("/", ".")


def read_imports(path: Path) -> set[str]:
    mods: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(line)
        if m:
            mods.add(m.group(1))
    return mods


def read_imports_closure(path: Path) -> set[str]:
    seen_files: set[Path] = set()
    seen_mods: set[str] = set()
    stack: list[Path] = [path]

    while stack:
        cur = stack.pop()
        if cur in seen_files:
            continue
        seen_files.add(cur)

        for mod in read_imports(cur):
            if mod in seen_mods:
                continue
            seen_mods.add(mod)

            if not mod.startswith("LogOS."):
                continue

            mod_path = ROOT / Path(mod.replace(".", "/") + ".agda")
            if mod_path.is_file():
                stack.append(mod_path)

    return seen_mods


def check_coverage(*, label: str, expected: list[str], discipline: Path) -> list[str]:
    if not discipline.is_file():
        return [f"{label}: missing discipline module: {discipline.relative_to(ROOT).as_posix()}"]

    imported = read_imports_closure(discipline)
    missing = [m for m in expected if m not in imported]
    return [f"{label}: missing import in discipline module: {m}" for m in missing]


def main() -> int:
    violations: list[str] = []

    log_dir = ROOT / "LogOS" / "LT" / "LOG"
    log_discipline = log_dir / "Discipline" / "PortsAsDisplayed.agda"
    log_strict_discipline = log_dir / "Discipline" / "StrictificationAsDisplayed.agda"
    excluded_log = {
        "Boundary2Cat.agda",
        "BoundaryDecode2Cat.agda",
        "Kernel2Cat.agda",
        "GuardedKernel2Cat.agda",
        "GuardedImplementation2Cat.agda",
        "GuardedImplementationContract2Cat.agda",
        "GuardedImplementationFlow2Cat.agda",
    }
    if log_dir.is_dir():
        expected_log: list[str] = []
        expected_log_strict: list[str] = []
        for p in sorted(log_dir.glob("*2Cat.agda")):
            if p.name in excluded_log:
                continue
            mod = module_from_path(p)
            if p.name in {"ClassicalLimit2Cat.agda", "StrictDecode2Cat.agda"}:
                expected_log_strict.append(mod)
            else:
                expected_log.append(mod)
        violations += check_coverage(
            label="LogOS.LT.LOG canonical",
            expected=expected_log,
            discipline=log_discipline,
        )
        violations += check_coverage(
            label="LogOS.LT.LOG strictification",
            expected=expected_log_strict,
            discipline=log_strict_discipline,
        )

    ports_dir = ROOT / "LogOS" / "Ports"
    ports_discipline = ports_dir / "Discipline" / "PortsAsDisplayed.agda"
    if ports_dir.is_dir():
        expected_ports: list[str] = []
        for p in sorted(ports_dir.rglob("*2Cat.agda")):
            if "_build" in p.parts:
                continue
            expected_ports.append(module_from_path(p))
        violations += check_coverage(
            label="LogOS.Ports canonical",
            expected=expected_ports,
            discipline=ports_discipline,
        )

    if violations:
        print("ports-as-displayed-coverage-check: FAIL", file=sys.stderr)
        print(
            "Policy: every canonical port surface must be routed through the canonical displayed discipline gate.",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    print("ports-as-displayed-coverage-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
