#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT_DEFAULT = ROOT / "docs" / "Generated" / "Equality_Surface_Map.md"
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")
SKIP_PREFIXES = ("module ", "open ", "import ", "record ", "data ", "private", "mutual", "where", "infix", "{-", "--")
QUARANTINE_PATTERNS = (
    "Strictification",
    "Definitional",
    "LogOS.LT.Ports.PortStack.Raw",
    "LogOS.LT.Ports.PortStack.ClassicalLimit",
    "LogOS.LT.Ports.PortSigStrictification",
    "LogOS.LT.LOG.ClassicalLimit2Cat",
    "LogOS.LT.LOG.StrictDecode2Cat",
    "LogOS.Ports.ClassicalLimit",
)
SURFACES = [
    "LogOS/API/LT.agda",
    "LogOS/API/Kernel.agda",
    "LogOS/API/Architecture.agda",
    "LogOS/API/Guarded.agda",
    "LogOS/API/Theorems/Core.agda",
    "LogOS/API/Strictification.agda",
    "LogOS/LT/Hom/Core.agda",
    "LogOS/LT/Hom/Strictification.agda",
    "LogOS/LT/TypeTheory/Surface.agda",
    "LogOS/LT/TypeTheory/Strictification.agda",
    "LogOS/LT/Ports/PortStack.agda",
    "LogOS/LT/Ports/PortStack/Raw.agda",
    "LogOS/LT/LOG/PortReindexing.agda",
    "LogOS/LT/LOG/PortReindexing/Strictification.agda",
    "LogOS/LT/Theorems/ArchitecturalNormalForm.agda",
    "LogOS/LT/Theorems/ArchitecturalNormalFormStrictification.agda",
    "LogOS/LT/Theorems/CenteringQuote.agda",
    "LogOS/Ports/IO.agda",
    "LogOS/Ports/BoundaryTransparency.agda",
]


def is_top_level_name(line: str) -> bool:
    if not line or line[:1].isspace():
        return False
    stripped = line.strip()
    if not stripped or any(stripped.startswith(p) for p in SKIP_PREFIXES):
        return False
    if ":" in stripped or "=" in stripped or " " in stripped or "\t" in stripped:
        return False
    if stripped == "_":
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


def exports_equality(lines: list[str]) -> bool:
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        if not is_top_level_name(line):
            idx += 1
            continue
        next_idx = next_nonempty(lines, idx + 1)
        if next_idx is None or not lines[next_idx].lstrip().startswith(":"):
            idx += 1
            continue
        type_block, end_idx = collect_type_block(lines, next_idx)
        if "≡" in type_block:
            return True
        idx = end_idx
    return False


def bool_mark(value: bool) -> str:
    return "yes" if value else "no"


def main() -> int:
    if len(sys.argv) > 2:
        print("usage: generate_equality_surface_map.py [OUT_PATH]", file=sys.stderr)
        return 2

    out = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else OUT_DEFAULT
    out.parent.mkdir(parents=True, exist_ok=True)

    rows: list[tuple[str, str, str, str, str, str, str]] = []

    for rel in SURFACES:
        path = ROOT / rel
        if not path.is_file():
            raise FileNotFoundError(rel)
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        imports = [m.group(1) for line in lines if (m := IMPORT_RE.match(line))]
        imports_quarantine = any(any(pattern in mod for pattern in QUARANTINE_PATTERNS) for mod in imports)
        imports_shadowing = any(mod == "LogOS.LT.Ports.PortStack.Raw" for mod in imports)
        exports_eq = exports_equality(lines)
        uses_setw = "Setω" in text
        exposes_raw_portstack = any(token in text for token in ("PortStack.Shadowing", "Listω", "Member", "HasPort")) and "UniquePortStack" not in text
        theorem_runtime = any(mod.startswith("LogOS.LT.Theorems.") for mod in imports)
        rows.append(
            (
                rel[:-5].replace("/", "."),
                bool_mark(imports_quarantine),
                bool_mark(exports_eq),
                bool_mark(uses_setw),
                bool_mark(imports_shadowing),
                bool_mark(exposes_raw_portstack),
                bool_mark(theorem_runtime),
            )
        )

    with out.open("w", encoding="utf-8") as f:
        f.write("<!--\n")
        f.write("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI\n")
        f.write("Copyright (C) 2026 AI.IMPACT GmbH\n")
        f.write("SPDX-License-Identifier: GPL-3.0-only\n")
        f.write("-->\n\n")
        f.write("# Equality Surface Map (Generated)\n\n")
        f.write("Generated from curated module surfaces by `scripts/generate_equality_surface_map.py`.\n\n")
        f.write("| Module | Imports quarantined lane? | Exports `≡`? | Uses `Setω`? | Imports raw `PortStack`? | Exposes raw `PortStack`? | Imports theorem runtime? |\n")
        f.write("| --- | --- | --- | --- | --- | --- | --- |\n")
        for row in rows:
            f.write("| " + " | ".join(f"`{cell}`" if i == 0 else cell for i, cell in enumerate(row)) + " |\n")

    shown = out.relative_to(ROOT).as_posix() if out.is_relative_to(ROOT) else str(out)
    print(f"generate-equality-surface-map: wrote {shown}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
