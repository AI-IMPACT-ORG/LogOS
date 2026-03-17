#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Default API stack exports must be uniqueness-first.
# - Raw `PortStack` / `HasPort` / duplicate-tag shadowing surfaces must not be
#   re-exported from `LogOS/API/**`.
# - Explicit raw/shadowing access belongs in non-default LT lanes.

set -euo pipefail

CHECK_NAME="public-portstack-uniqueness-check"
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
API_DIR = ROOT / "LogOS" / "API"
ALLOWLIST = ROOT / "scripts" / "public_portstack_duplicate_allowlist.txt"

RAW_PUBLIC_SYMBOLS = {
    "PortStack",
    "HasPort",
    "mkHasPort",
    "hasSingleton",
    "hasHead",
    "hasThere",
    "getObj",
    "getHom",
    "forgetPort",
    "Substack",
    "forgetSubstack",
    "pullbackPortStack",
    "Listω",
    "Member",
    "here",
    "there",
    "SingletonPort",
    "singletonPort",
}

SKIP_PREFIXES = ("module ", "open ", "import ", "record ", "data ", "private", "mutual", "where", "infix", "{-", "--")


def parse_allowlist(path: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    if not path.is_file():
        return out
    for i, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        cols = raw.split("\t", 1)
        if len(cols) != 2 or not cols[1].strip():
            print(f"{path.relative_to(ROOT)}:{i}: expected <qualified-symbol><TAB><reason>", file=sys.stderr)
            raise SystemExit(1)
        out[cols[0].strip()] = cols[1].strip()
    return out


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


def is_top_level_name(line: str) -> bool:
    if not line or line[:1].isspace():
        return False
    stripped = line.strip()
    if not stripped or any(stripped.startswith(p) for p in SKIP_PREFIXES):
        return False
    if ":" in stripped or "=" in stripped or " " in stripped or "\t" in stripped:
        return False
    return True


def next_nonempty(lines: list[str], start: int) -> int | None:
    for idx in range(start, len(lines)):
        if lines[idx].strip():
            return idx
    return None


def collect_type_block(lines: list[str], colon_idx: int) -> tuple[str, int]:
    block: list[str] = []
    idx = colon_idx
    while idx < len(lines):
        line = lines[idx]
        if idx > colon_idx and line and not line[:1].isspace() and not line.lstrip().startswith(":"):
            break
        block.append(line)
        idx += 1
    return "\n".join(block), idx


allowlist = parse_allowlist(ALLOWLIST)
violations: list[str] = []
seen_allowlist_targets: set[str] = set()

for path in sorted(API_DIR.rglob("*.agda")):
    rel = path.relative_to(ROOT).as_posix()
    module_name = module_from_path(path)
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    for m in re.finditer(r"open\s+import\s+[A-Za-z0-9_.']+\s+public\s+using\s*\((.*?)\)", text, flags=re.S):
        body = m.group(1)
        for symbol in RAW_PUBLIC_SYMBOLS:
            if re.search(rf"(^|[;\s(]){re.escape(symbol)}($|[;\s,)])", body):
                violations.append(f"{rel}: default API re-exports raw port-stack symbol {symbol}")

    idx = 0
    while idx < len(lines):
        line = lines[idx]
        if not is_top_level_name(line):
            idx += 1
            continue
        symbol = line.strip()
        next_idx = next_nonempty(lines, idx + 1)
        if next_idx is None or not lines[next_idx].lstrip().startswith(":"):
            idx += 1
            continue
        type_block, end_idx = collect_type_block(lines, next_idx)
        normalized = " ".join(part.split("--", 1)[0].strip() for part in type_block.splitlines() if part.strip())
        qualified = f"{module_name}.{symbol}"

        if symbol.endswith("Stack") and "PortStack" in normalized and "UniquePortStack" not in normalized:
            if qualified not in allowlist:
                violations.append(f"{rel}:{idx + 1}: default API stack export is raw PortStack, not UniquePortStack: {qualified}")
            else:
                seen_allowlist_targets.add(qualified)

        if symbol.endswith("Port") and "HasPort" in normalized and "UniquePort" not in normalized:
            if qualified not in allowlist:
                violations.append(f"{rel}:{idx + 1}: default API port export is raw HasPort, not UniquePort: {qualified}")
            else:
                seen_allowlist_targets.add(qualified)

        idx = end_idx

for qualified in allowlist:
    if qualified not in seen_allowlist_targets:
        violations.append(f"allowlist entry does not correspond to a current raw public API export: {qualified}")

if violations:
    print("public-portstack-uniqueness-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("public-portstack-uniqueness-check: OK")
PY
