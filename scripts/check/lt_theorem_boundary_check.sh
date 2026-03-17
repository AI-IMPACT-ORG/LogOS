#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Non-theorem LT modules may only import theorem modules when the dependency is
#   explicitly recorded as load-bearing architecture.

set -euo pipefail

CHECK_NAME="lt-theorem-boundary-check"
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
LT_DIR = ROOT / "LogOS" / "LT"
MANIFEST = ROOT / "scripts" / "lt_theorem_runtime_manifest.tsv"
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


manifest: dict[str, str] = {}
if not MANIFEST.is_file():
    print(f"lt-theorem-boundary-check: FAIL", file=sys.stderr)
    print(f"  - missing manifest {MANIFEST.relative_to(ROOT).as_posix()}", file=sys.stderr)
    raise SystemExit(1)

for i, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    cols = raw.split("\t", 1)
    if len(cols) != 2 or not cols[1].strip():
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: expected <module><TAB><justification>", file=sys.stderr)
        raise SystemExit(1)
    manifest[cols[0].strip()] = cols[1].strip()

violations: list[str] = []
seen_manifest: set[str] = set()

for path in sorted(LT_DIR.rglob("*.agda")):
    if "_build" in path.parts:
        continue
    rel = path.relative_to(ROOT).as_posix()
    module_name = module_from_path(path)
    if module_name.startswith("LogOS.LT.Theorems."):
        continue
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        m = IMPORT_RE.match(line)
        if not m:
            continue
        mod = m.group(1)
        if not mod.startswith("LogOS.LT.Theorems."):
            continue
        if module_name not in manifest:
            violations.append(f"{rel}:{i}: non-theorem LT module imports theorem module without manifest entry: {mod}")
        else:
            seen_manifest.add(module_name)

for module_name in manifest:
    if module_name not in seen_manifest:
        violations.append(f"manifest entry has no current non-theorem theorem import: {module_name}")

if violations:
    print("lt-theorem-boundary-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("lt-theorem-boundary-check: OK")
PY
