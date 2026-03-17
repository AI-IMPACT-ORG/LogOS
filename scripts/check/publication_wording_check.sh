#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Published surfaces must not advertise provisional or throwaway status with
#   words like `TEMP`, `WIP`, `placeholder`, or unqualified `experimental`.
# - Narrow exceptions are tracked in an explicit wording allowlist.

set -euo pipefail

CHECK_NAME="publication-wording-check"
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
MANIFEST = ROOT / "scripts" / "publication_surface.tsv"
ALLOWLIST = ROOT / "scripts" / "publication_wording_allowlist.tsv"
BAD_RE = re.compile(r"\b(?:TEMP|WIP|placeholder|experimental)\b", re.IGNORECASE)
TEXT_SUFFIXES = {".agda", ".md", ".tex"}


def load_allowlist(path: Path) -> set[str]:
    if not path.is_file():
        return set()
    out: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        cols = raw.split("\t", 1)
        if len(cols) == 2 and cols[0].strip():
            out.add(cols[0].strip())
    return out


allowlist = load_allowlist(ALLOWLIST)
targets: list[Path] = []

for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    tier, kind, rel, _note = [part.strip() for part in raw.split("\t")]
    if tier != "published":
        continue
    path = ROOT / rel
    if kind == "file":
        targets.append(path)
    else:
        for child in sorted(path.rglob("*")):
            if "_build" in child.parts or not child.is_file():
                continue
            if child.suffix in TEXT_SUFFIXES or child.name.endswith(".lagda.md"):
                targets.append(child)

violations: list[str] = []

for path in sorted(set(targets)):
    rel = path.relative_to(ROOT).as_posix()
    if rel in allowlist:
        continue
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        continue
    for i, line in enumerate(text.splitlines(), start=1):
        m = BAD_RE.search(line)
        if m:
            violations.append(f"{rel}:{i}: banned publication wording {m.group(0)!r}")

if violations:
    print("publication-wording-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("publication-wording-check: OK")
PY
