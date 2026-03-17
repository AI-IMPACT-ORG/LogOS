#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Template packaging equalities like `displayed≡`, `withPort≡`, and `forget≡`
#   belong only in explicit `Definitional`, `Strictification`, or `Checks`
#   lanes.
# - The default surface may use the underlying template constructors, but must
#   not expose or depend on these packaging-equality names directly.

set -euo pipefail

CHECK_NAME="packaging-equality-check"
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
LOGOS_DIR = ROOT / "LogOS"
BANNED = re.compile(r"(?<![A-Za-z0-9_.'-])(displayed≡|withPort≡|forget≡)(?![A-Za-z0-9_.'-])")
ALLOWED_EXACT = {
    "LogOS/LT/Ports/Template/Singleton2Cat.agda",
    "LogOS/LT/Ports/Template/Stack2Cat.agda",
}


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)

    while i < n:
        if depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue

        if text.startswith("{-", i):
            depth += 1
            i += 2
            continue

        if depth > 0:
            if text.startswith("{-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-}", i):
                depth -= 1
                i += 2
                continue
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def is_allowed(path: Path) -> bool:
    rel_path = rel(path)
    if rel_path in ALLOWED_EXACT:
        return True
    if rel_path.endswith("Definitional.agda") or rel_path.endswith("Strictification.agda"):
        return True
    parts = path.parts
    return "Checks" in parts


violations: list[str] = []

for path in sorted(LOGOS_DIR.rglob("*.agda")):
    if "_build" in path.parts or is_allowed(path):
        continue
    text = strip_comments(path.read_text(encoding="utf-8"))
    if BANNED.search(text):
        violations.append(rel(path))

if violations:
    print("packaging-equality-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - packaging equality leaked outside quarantine lane: {item}", file=sys.stderr)
    raise SystemExit(1)

print("packaging-equality-check: OK")
PY
