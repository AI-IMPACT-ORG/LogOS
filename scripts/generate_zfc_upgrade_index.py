#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "scripts" / "zfc_upgrade_manifest.tsv"


def load_rows() -> list[tuple[str, str, str, str, str]]:
    rows: list[tuple[str, str, str, str, str]] = []
    for raw in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        kind, module_name, symbol, ledger_anchor, status = raw.split("\t")
        rows.append((kind, module_name, symbol, ledger_anchor, status))
    return rows


def main() -> int:
    if len(sys.argv) > 2:
        print("usage: generate_zfc_upgrade_index.py [OUT_PATH]", file=sys.stderr)
        return 2

    out_path = Path(sys.argv[1]) if len(sys.argv) == 2 else Path("docs/Generated/ZFC_Upgrade_Index.md")
    out = (ROOT / out_path).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)

    rows = load_rows()
    grouped: dict[str, list[tuple[str, str, str, str]]] = defaultdict(list)
    for kind, module_name, symbol, ledger_anchor, status in rows:
        grouped[kind].append((module_name, symbol, ledger_anchor, status))

    order = ["assumption", "ledger", "upgrade-record", "upgrade-builder", "theorem-upgrade"]

    with out.open("w", encoding="utf-8") as f:
        f.write("<!--\n")
        f.write("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI\n")
        f.write("Copyright (C) 2026 AI.IMPACT GmbH\n")
        f.write("SPDX-License-Identifier: GPL-3.0-only\n")
        f.write("-->\n\n")
        f.write("# ZFC Upgrade Index (Generated)\n\n")
        f.write("Generated from `scripts/zfc_upgrade_manifest.tsv` by `scripts/generate_zfc_upgrade_index.py`.\n\n")
        f.write("This index tracks explicit ZFC upgrade/assumption packaging points and where the assumptions ledger expects them.\n\n")
        for kind in order:
            items = sorted(grouped.get(kind, []), key=lambda item: (item[0], item[1]))
            if not items:
                continue
            f.write(f"## {kind}\n\n")
            for module_name, symbol, ledger_anchor, status in items:
                path = module_name.replace(".", "/") + ".agda"
                f.write(f"- `{symbol}`\n")
                f.write(f"  - Module: `{path}`\n")
                f.write(f"  - Ledger anchor: `{ledger_anchor}`\n")
                f.write(f"  - Status: `{status}`\n")
            f.write("\n")

    try:
        shown = out.relative_to(ROOT).as_posix()
    except ValueError:
        shown = str(out)
    print(f"generate-zfc-upgrade-index: wrote {shown}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
