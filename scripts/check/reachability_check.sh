#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - No orphaned core modules: every non-Host core Agda module must be reachable
#   from explicit policy/check roots or from the canonical spec roots.

set -euo pipefail

CHECK_NAME="reachability-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import pathlib
import re
import sys
from collections import defaultdict, deque

ROOT = pathlib.Path(".").resolve()


def module_from_path(path: pathlib.Path) -> str:
    rel = path.relative_to(ROOT)
    s = rel.as_posix()
    if s.endswith(".agda"):
        s = s[: -len(".agda")]
    elif s.endswith(".lagda.md"):
        s = s[: -len(".lagda.md")]
    else:
        raise ValueError(f"unexpected module path suffix: {rel}")
    return s.replace("/", ".")


IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")


def read_imports_agda(path: pathlib.Path) -> list[str]:
    out: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def extract_docs_agda_blocks(path: pathlib.Path) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    inside = False
    out: list[str] = []
    for line in lines:
        if re.match(r"^\s*```\s*agda\s*$", line):
            inside = True
            continue
        if re.match(r"^\s*```\s*$", line) and inside:
            inside = False
            continue
        if inside:
            out.append(line)
    return out


def read_imports_docs(path: pathlib.Path) -> list[str]:
    out: list[str] = []
    for line in extract_docs_agda_blocks(path):
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def is_core_agda(path: pathlib.Path) -> bool:
    rel = path.relative_to(ROOT).as_posix()
    if not rel.startswith("LogOS/"):
        return False
    if rel.startswith("LogOS/Host/"):
        return False
    if rel.startswith("LogOS/Checks/"):
        return False
    if rel.startswith("LogOS/Apps/"):
        return False
    if rel.startswith("LogOS/Adapters/"):
        return False
    return True


def main() -> int:
    modules: dict[str, pathlib.Path] = {}

    logos_dir = ROOT / "LogOS"
    if logos_dir.is_dir():
        for p in logos_dir.rglob("*.agda"):
            if "_build" in p.parts:
                continue
            modules[module_from_path(p)] = p

    docs_dir = ROOT / "docs"
    if docs_dir.is_dir():
        for p in docs_dir.rglob("*.lagda.md"):
            if "_build" in p.parts:
                continue
            modules[module_from_path(p)] = p

    if not modules:
        print("reachability-check: no modules found", file=sys.stderr)
        return 1

    edges: dict[str, set[str]] = defaultdict(set)
    for mod, path in modules.items():
        deps: list[str]
        if path.suffix == ".agda":
            deps = read_imports_agda(path)
        else:
            deps = read_imports_docs(path)
        for dep in deps:
            if dep in modules:
                edges[mod].add(dep)

    roots: set[str] = set()

    checks_reachability = ROOT / "LogOS" / "Checks" / "Reachability"
    if checks_reachability.is_dir():
        for check_root in sorted(checks_reachability.glob("*.agda")):
            roots.add(module_from_path(check_root))

    for sd in (
        ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md",
        ROOT / "docs" / "Core" / "Spec" / "LogOS_Specification.lagda.md",
    ):
        if sd.exists():
            roots.add(module_from_path(sd))

    if not roots:
        print(
            "reachability-check: no roots found (expected LogOS/Checks/Reachability/*.agda and/or docs/Core/Spec/*.lagda.md)",
            file=sys.stderr,
        )
        return 1

    reachable: set[str] = set()
    queue: deque[str] = deque(sorted(roots))

    while queue:
        mod = queue.popleft()
        if mod in reachable:
            continue
        reachable.add(mod)
        for dep in edges.get(mod, ()):
            if dep not in reachable:
                queue.append(dep)

    unreachable_core: list[str] = []
    for mod, path in modules.items():
        if mod in reachable:
            continue
        if path.suffix != ".agda":
            continue
        if is_core_agda(path):
            unreachable_core.append(mod)

    if unreachable_core:
        print("reachability-check: FAIL (unreachable core modules)", file=sys.stderr)
        print(
            "Rule: every non-Host core module must be reachable from an explicit spec/check root.",
            file=sys.stderr,
        )
        for mod in sorted(unreachable_core):
            print(f"  - {mod}", file=sys.stderr)
        return 1

    print("reachability-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
