#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Strictification/definitional/raw-shadowing imports must not silently drift
#   into default LT/Ports/Apps lanes.
# - Any such dependency outside explicit quarantine lanes must be allowlisted
#   with a one-line architectural justification.

set -euo pipefail

CHECK_NAME="strictification-boundary-check"
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
MANIFEST = ROOT / "scripts" / "strictification_boundary_allowlist.tsv"
SCAN_ROOTS = [ROOT / "LogOS" / "LT", ROOT / "LogOS" / "Ports", ROOT / "LogOS" / "Apps"]
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")
QUARANTINED_PATTERNS = (
    "Strictification",
    "Definitional",
    "LogOS.LT.Ports.PortStack.Raw",
    "LogOS.LT.Ports.PortStack.ClassicalLimit",
    "LogOS.LT.Ports.PortSigStrictification",
    "LogOS.LT.LOG.ClassicalLimit2Cat",
    "LogOS.LT.LOG.StrictDecode2Cat",
    "LogOS.Ports.ClassicalLimit",
)
SKIP_MARKERS = ("Strictification", "Definitional", "Shadowing", "Raw", "ClassicalLimit")


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


def load_manifest(path: Path) -> dict[str, str]:
    if not path.is_file():
        print("strictification-boundary-check: FAIL", file=sys.stderr)
        print(f"  - missing allowlist {path.relative_to(ROOT).as_posix()}", file=sys.stderr)
        raise SystemExit(1)
    out: dict[str, str] = {}
    for i, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        cols = raw.split("\t", 1)
        if len(cols) != 2 or not cols[1].strip():
            print(f"{path.relative_to(ROOT)}:{i}: expected <module><TAB><justification>", file=sys.stderr)
            raise SystemExit(1)
        out[cols[0].strip()] = cols[1].strip()
    return out


def is_quarantined_import(module_name: str) -> bool:
    return any(pattern in module_name for pattern in QUARANTINED_PATTERNS)


allowlist = load_manifest(MANIFEST)
seen_allowlist: set[str] = set()
violations: list[str] = []

for scan_root in SCAN_ROOTS:
    for path in sorted(scan_root.rglob("*.agda")):
        if "_build" in path.parts:
            continue
        module_name = module_from_path(path)
        if any(marker in module_name for marker in SKIP_MARKERS):
            continue
        if module_name.startswith("LogOS.Checks."):
            continue
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            imported = m.group(1)
            if not is_quarantined_import(imported):
                continue
            if module_name not in allowlist:
                rel = path.relative_to(ROOT).as_posix()
                violations.append(
                    f"{rel}:{i}: default-lane module imports quarantined surface without allowlist entry: {imported}"
                )
            else:
                seen_allowlist.add(module_name)

for module_name in sorted(allowlist):
    if module_name not in seen_allowlist:
        violations.append(f"allowlist entry has no current quarantined import: {module_name}")

if violations:
    print("strictification-boundary-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("strictification-boundary-check: OK")
PY
