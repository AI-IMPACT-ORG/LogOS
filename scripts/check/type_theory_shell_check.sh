#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `LogOS.LT.TypeTheory` is a shell view over deeper LT implementations.
# - Non-quarantine shell modules should stay re-export only; substantial logic
#   belongs in the underlying LT layers.

set -euo pipefail

CHECK_NAME="type-theory-shell-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

from pathlib import Path

ROOT = Path(".").resolve()
FILES = [
    "LogOS/LT/TypeTheory.agda",
    "LogOS/LT/TypeTheory/Intensional.agda",
    "LogOS/LT/TypeTheory/Ports.agda",
    "LogOS/LT/TypeTheory/Reflection.agda",
    "LogOS/LT/TypeTheory/Stack.agda",
]


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


ALLOWED_PREFIXES = (
    "{-#",
    "module ",
    "import ",
    "open ",
    "private",
    "infix ",
    "infixl ",
    "infixr ",
)
CONTINUATION_PREFIXES = ("(", ";", ")", "renaming", "using", "hiding")

violations: list[str] = []

for rel in FILES:
    path = ROOT / rel
    if not path.is_file():
        violations.append(f"{rel}: missing shell module")
        continue

    text = strip_comments(path.read_text(encoding="utf-8"))
    in_import_block = False

    for i, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            in_import_block = False
            continue

        if line.startswith(ALLOWED_PREFIXES):
            in_import_block = line.startswith(("import ", "open "))
            continue

        if in_import_block and line.startswith(CONTINUATION_PREFIXES):
            continue

        violations.append(
            f"{rel}:{i}: non-shell content in type-theory shell module ({line})"
        )
        in_import_block = False

if violations:
    print("type-theory-shell-check: FAIL")
    print(
        "Policy: non-quarantine LogOS.LT.TypeTheory modules should stay as re-export shells over deeper LT implementations."
    )
    for item in violations:
        print(f"  - {item}")
    raise SystemExit(1)

print("type-theory-shell-check: OK")
PY
