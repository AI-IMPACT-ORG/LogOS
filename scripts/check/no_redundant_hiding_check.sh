#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Forbid empty `hiding ()` clauses in `open` / `open import` statements.
# - Forbid empty `using ()` clauses in `open` / `open import` statements.
# - Rationale: both are no-ops; keeping them around is pure noise and tends to accumulate as a “satisfy CI”
#   workaround rather than an intentional dependency boundary.

set -euo pipefail

CHECK_NAME="no-redundant-hiding-check"
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


def strip_agda_comments_preserve_newlines(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue

        if block_depth > 0:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == "-" and nxt == "}":
                block_depth -= 1
                i += 2
                continue
            if ch == "{" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        if ch == "{" and nxt == "-":
            block_depth = 1
            i += 2
            continue

        if ch == "-" and nxt == "-":
            i = text.find("\n", i)
            if i == -1:
                break
            out.append("\n")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


OPEN_START_RE = re.compile(r"^\s*open\b")
EMPTY_HIDING_RE = re.compile(r"\bhiding\s*\(\s*\)")
EMPTY_USING_RE = re.compile(r"\busing\s*\(\s*\)")


def leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def iter_agda_files() -> list[Path]:
    logos_dir = ROOT / "LogOS"
    if not logos_dir.is_dir():
        return []
    return [p for p in sorted(logos_dir.rglob("*.agda")) if "_build" not in p.parts]


def main() -> int:
    violations: list[str] = []

    for path in iter_agda_files():
        rel = path.relative_to(ROOT).as_posix()
        text = path.read_text(encoding="utf-8")
        stripped = strip_agda_comments_preserve_newlines(text)
        lines = stripped.splitlines()

        i = 0
        while i < len(lines):
            line = lines[i]
            if not OPEN_START_RE.match(line):
                i += 1
                continue

            indent0 = leading_spaces(line)
            stmt_lines = [line]
            j = i + 1
            while j < len(lines):
                nxt = lines[j]
                if nxt.strip() == "":
                    stmt_lines.append(nxt)
                    j += 1
                    continue

                indent = leading_spaces(nxt)
                nxt_stripped = nxt.lstrip()
                if indent > indent0:
                    stmt_lines.append(nxt)
                    j += 1
                    continue

                # Rare style: continuation line aligned with the `open` line.
                if indent == indent0 and nxt_stripped.startswith(("(", ";")):
                    stmt_lines.append(nxt)
                    j += 1
                    continue

                break

            stmt = "\n".join(stmt_lines)
            if EMPTY_HIDING_RE.search(stmt):
                lineno = i + 1
                head = stmt_lines[0].strip()
                violations.append(
                    f"{rel}:{lineno}: empty `hiding ()` in open statement: {head}"
                )
            if EMPTY_USING_RE.search(stmt):
                lineno = i + 1
                head = stmt_lines[0].strip()
                violations.append(
                    f"{rel}:{lineno}: empty `using ()` in open statement: {head}"
                )

            i = j

    if violations:
        print(f"{'no-redundant-hiding-check'}: FAIL", file=sys.stderr)
        print("Found empty `hiding ()` / `using ()` clauses:", file=sys.stderr)
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        print("\nFix: delete empty `hiding ()` / `using ()` clauses.", file=sys.stderr)
        return 1

    print("no-redundant-hiding-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
