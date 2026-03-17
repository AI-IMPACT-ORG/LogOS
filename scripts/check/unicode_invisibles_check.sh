#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="unicode-invisibles-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path

CHECK_NAME = "unicode-invisibles-check"
ROOT = Path(".").resolve()

# Policy: forbid invisible/bidi control characters in source and docs.
#
# Rationale: these characters are hard to review and can hide meaning changes
# (Trojan Source style issues). Keep the repo auditable.
FORBIDDEN_CODEPOINTS: dict[int, str] = {
    # Zero-width / invisible.
    0x200B: "ZERO WIDTH SPACE",
    0x200C: "ZERO WIDTH NON-JOINER",
    0x200D: "ZERO WIDTH JOINER",
    0x2060: "WORD JOINER",
    0xFEFF: "ZERO WIDTH NO-BREAK SPACE (BOM)",
    # Non-breaking space (looks like a normal space).
    0x00A0: "NO-BREAK SPACE",
    # Bidi controls (Trojan Source).
    0x200E: "LEFT-TO-RIGHT MARK",
    0x200F: "RIGHT-TO-LEFT MARK",
    0x061C: "ARABIC LETTER MARK",
    0x202A: "LEFT-TO-RIGHT EMBEDDING",
    0x202B: "RIGHT-TO-LEFT EMBEDDING",
    0x202C: "POP DIRECTIONAL FORMATTING",
    0x202D: "LEFT-TO-RIGHT OVERRIDE",
    0x202E: "RIGHT-TO-LEFT OVERRIDE",
    0x2066: "LEFT-TO-RIGHT ISOLATE",
    0x2067: "RIGHT-TO-LEFT ISOLATE",
    0x2068: "FIRST STRONG ISOLATE",
    0x2069: "POP DIRECTIONAL ISOLATE",
}

SCAN_SUFFIXES = {
    ".agda",
    ".md",
    ".sh",
    ".txt",
    ".tex",
    ".yml",
    ".yaml",
    ".toml",
}

SCAN_BASENAMES = {
    "Makefile",
}


@dataclass(frozen=True)
class Hit:
    rel: str
    line: int
    col: int
    codepoint: int
    char_name: str


def should_scan(path: Path) -> bool:
    if not path.is_file():
        return False
    if "_build" in path.parts:
        return False
    if ".git" in path.parts:
        return False
    if path.name in SCAN_BASENAMES:
        return True
    if path.name.endswith(".lagda.md"):
        return True
    return path.suffix in SCAN_SUFFIXES


def scan_text(rel: str, text: str) -> list[Hit]:
    hits: list[Hit] = []
    line = 1
    col = 1
    for ch in text:
        cp = ord(ch)
        if cp in FORBIDDEN_CODEPOINTS:
            name = FORBIDDEN_CODEPOINTS[cp]
            # Use Unicode database if available for extra confidence.
            try:
                db_name = unicodedata.name(ch)
                if db_name and db_name != name:
                    name = f"{name} / {db_name}"
            except ValueError:
                pass
            hits.append(Hit(rel=rel, line=line, col=col, codepoint=cp, char_name=name))
        if ch == "\n":
            line += 1
            col = 1
        else:
            col += 1
    return hits


def main() -> int:
    hits: list[Hit] = []

    for path in sorted(ROOT.rglob("*")):
        if not should_scan(path):
            continue
        rel = path.relative_to(ROOT).as_posix()
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as e:
            print(f"{CHECK_NAME}: FAIL", file=sys.stderr)
            print(f"Policy: all scanned files must be valid UTF-8 text ({rel}: {e}).", file=sys.stderr)
            return 1

        hits.extend(scan_text(rel, text))

    if hits:
        print(f"{CHECK_NAME}: FAIL", file=sys.stderr)
        print(
            "Policy: forbid invisible / bidi control characters in source and docs.",
            file=sys.stderr,
        )
        print("Violations:", file=sys.stderr)
        for h in hits[:200]:
            print(
                f"  - {h.rel}:{h.line}:{h.col}: U+{h.codepoint:04X} {h.char_name}",
                file=sys.stderr,
            )
        if len(hits) > 200:
            print(f"  - … and {len(hits) - 200} more", file=sys.stderr)
        return 1

    print(f"{CHECK_NAME}: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY

