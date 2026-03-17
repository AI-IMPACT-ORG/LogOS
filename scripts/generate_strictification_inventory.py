#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "strictification_contract_manifest.tsv"
OUT_DEFAULT = ROOT / "docs" / "Generated" / "Strictification_Inventory.md"


def main() -> int:
    if len(sys.argv) > 2:
        print("usage: generate_strictification_inventory.py [OUT_PATH]", file=sys.stderr)
        return 2

    out = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else OUT_DEFAULT
    out.parent.mkdir(parents=True, exist_ok=True)

    rows: list[tuple[str, str, str, str, str]] = []
    for i, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        cols = raw.split("\t")
        if len(cols) != 5:
            raise ValueError(f"{MANIFEST.relative_to(ROOT)}:{i}: expected 5 tab-separated columns")
        rows.append(tuple(col.strip() for col in cols))

    with out.open("w", encoding="utf-8") as f:
        f.write("<!--\n")
        f.write("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI\n")
        f.write("Copyright (C) 2026 AI.IMPACT GmbH\n")
        f.write("SPDX-License-Identifier: GPL-3.0-only\n")
        f.write("-->\n\n")
        f.write("# Strictification Inventory (Generated)\n\n")
        f.write("Generated from `scripts/strictification_contract_manifest.tsv`.\n\n")
        f.write("| Module | Strict object | Downgrade to `≈` | Downgrade to `⊑` | Law or anchor |\n")
        f.write("| --- | --- | --- | --- | --- |\n")
        for row in rows:
            cells = [f"`{row[0]}`", f"`{row[1]}`", f"`{row[2]}`", f"`{row[3]}`", f"`{row[4]}`"]
            f.write("| " + " | ".join(cells) + " |\n")

    shown = out.relative_to(ROOT).as_posix() if out.is_relative_to(ROOT) else str(out)
    print(f"generate-strictification-inventory: wrote {shown}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
