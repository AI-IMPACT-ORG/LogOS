#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The live repository uses the current semantic docs taxonomy.
# - Retired audience-split or pre-migration doc path families may remain only
#   in historical material kept out of the live repository.

set -euo pipefail

CHECK_NAME="docs-taxonomy-check"
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

SCAN_ROOTS = [
    ROOT / "README.md",
    ROOT / "docs",
    ROOT / "LogOS",
    ROOT / "scripts",
    ROOT / "Makefile",
    ROOT / ".github",
]

TEXT_SUFFIXES = {
    ".agda",
    ".cff",
    ".md",
    ".py",
    ".sh",
    ".tex",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}

LEGACY_RE = re.compile(r"\bdocs/(AI|Humans|Views)(?:/|\b)")

violations: list[str] = []

def iter_paths(root: Path) -> list[Path]:
    if root.is_file():
        return [root]
    if not root.exists():
        return []
    out: list[Path] = []
    for path in root.rglob("*"):
        if "_build" in path.parts:
            continue
        if path.is_file() and path.suffix in TEXT_SUFFIXES:
            out.append(path)
    return out

for scan_root in SCAN_ROOTS:
    for path in iter_paths(scan_root):
        rel = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        for i, line in enumerate(text.splitlines(), start=1):
            m = LEGACY_RE.search(line)
            if m:
                violations.append(f"{rel}:{i}: {m.group(0)}")

if violations:
    print("docs-taxonomy-check: FAIL", file=sys.stderr)
    print("Policy: canonical lanes must use the current docs taxonomy.", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("docs-taxonomy-check: OK")
PY
