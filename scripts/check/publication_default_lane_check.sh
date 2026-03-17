#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Published/default LT, Ports, and API surfaces should not import
#   `Definitional` or `Strictification` lanes directly unless they sit on an
#   explicit shrinking allowlist with a one-line justification.

set -euo pipefail

CHECK_NAME="publication-default-lane-check"
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
ALLOWLIST = ROOT / "scripts" / "publication_default_lane_allowlist.tsv"
SCAN_ROOTS = [ROOT / "LogOS" / "API", ROOT / "LogOS" / "LT", ROOT / "LogOS" / "Ports"]
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")
SKIP_MARKERS = (
    "Definitional",
    "Strictification",
    ".Checks.",
    ".Discipline.",
    ".ClassicalLimit",
    ".Raw",
    "PortSigStrictification",
)


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


allowlist: dict[str, str] = {}
for i, raw in enumerate(ALLOWLIST.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    cols = raw.split("\t", 1)
    if len(cols) != 2 or not cols[1].strip():
        print(f"scripts/publication_default_lane_allowlist.tsv:{i}: expected <module><TAB><justification>", file=sys.stderr)
        raise SystemExit(1)
    allowlist[cols[0].strip()] = cols[1].strip()

violations: list[str] = []
seen_allowlist: set[str] = set()

for root in SCAN_ROOTS:
    for path in sorted(root.rglob("*.agda")):
        if "_build" in path.parts:
            continue
        module_name = module_from_path(path)
        if any(marker in module_name for marker in SKIP_MARKERS):
            continue
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            imported = m.group(1)
            if "Definitional" not in imported and "Strictification" not in imported:
                continue
            if module_name not in allowlist:
                rel = path.relative_to(ROOT).as_posix()
                violations.append(f"{rel}:{i}: default-lane module imports quarantined surface without publication allowlist entry: {imported}")
            else:
                seen_allowlist.add(module_name)

for module_name in sorted(allowlist):
    if module_name not in seen_allowlist:
        violations.append(f"publication allowlist entry has no current quarantined import: {module_name}")

if violations:
    print("publication-default-lane-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("publication-default-lane-check: OK")
PY
