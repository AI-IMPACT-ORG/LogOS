#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

OUT_PATH="${1:-docs/Generated/Architecture_Clarity_Index.md}"
OUT_DIR="$(dirname "${OUT_PATH}")"
mkdir -p "${OUT_DIR}"

OUT_PATH="${OUT_PATH}" python3 - <<'PY'
from __future__ import annotations

import os
import re
from pathlib import Path

ROOT = Path(".").resolve()
OUT = (ROOT / Path(os.environ["OUT_PATH"])).resolve()

MODULE_MAP = [
    ("LogOS.LT.CodeCompat", "LogOS.LT.BoundaryImplementation"),
    ("LogOS.LT.LOG.Realiser2Cat", "LogOS.LT.LOG.Implementation2Cat"),
    ("LogOS.LT.LOG.RealiserContract2Cat", "LogOS.LT.LOG.ImplementationContract2Cat"),
    ("LogOS.LT.LOG.RealiserFlow2Cat", "LogOS.LT.LOG.ImplementationFlow2Cat"),
    ("LogOS.LT.LOG.RealiserDecode2Cat", "LogOS.LT.LOG.ImplementationDecode2Cat"),
    ("LogOS.LT.LOG.EncodePort2CatG", "LogOS.LT.LOG.ArchitectureEncode2Cat"),
    ("LogOS.LT.LOG.QuotePort2CatG", "LogOS.LT.LOG.ArchitectureQuote2Cat"),
    ("LogOS.LT.LOG.QuotePort2CatG.Displayed", "LogOS.LT.LOG.ArchitectureQuote2Cat.Displayed"),
    ("LogOS.LT.LOG.FlowContract2CatG", "LogOS.LT.LOG.ArchitectureFlowContract2Cat"),
    ("LogOS.LT.LOG.BulkBoundary2CatG", "LogOS.LT.LOG.ArchitectureBulkBoundary2Cat"),
    ("LogOS.LT.LOG.BulkBoundaryContract2CatG", "LogOS.LT.LOG.ArchitectureBulkBoundaryContract2Cat"),
    ("LogOS.API.Ports.LTDecorationsLOGG", "LogOS.API.Ports.LTDecorationsArchitecture"),
    ("LogOS.API.Ports.UniversalityLOGG", "LogOS.API.Ports.UniversalityArchitecture"),
    ("LogOS.Ports.Universality.BudgetBus2CatG", "LogOS.Ports.Universality.ArchitectureBudgetBus2Cat"),
    ("LogOS.Ports.Universality.FlowBudget2CatG", "LogOS.Ports.Universality.ArchitectureFlowBudget2Cat"),
]

IDENTIFIER_MAP = [
    ("CodeCompat", "BoundaryImplementation"),
    ("RealiserDisplayed", "ImplementationDisplayed"),
    ("RealiserTag", "ImplementationTag"),
    ("forgetRealiser", "forgetImplementation"),
    ("RealiserContractStack", "ImplementationContractStack"),
    ("RealiserContractKernel", "ImplementationContractKernel"),
    ("RealiserFlowStack", "ImplementationFlowStack"),
    ("realiserSig", "implementationSig"),
    ("realiserSingleton", "implementationSingleton"),
    ("mapCode", "implementCode (preferred alias)"),
    ("decode-mapCode", "decode-implementsBoundary (preferred alias)"),
]

LEGACY_IDENTIFIERS = {
    "CodeCompat",
    "RealiserDisplayed",
    "RealiserTag",
    "forgetRealiser",
    "RealiserContractStack",
    "RealiserContractKernel",
    "RealiserFlowStack",
    "realiserSig",
    "realiserSingleton",
    "LTDecorationsLOGG",
    "UniversalityLOGG",
}

LEGACY_MODULES = {
    "LogOS.LT.CodeCompat",
    "LogOS.LT.LOG.Realiser2Cat",
    "LogOS.LT.LOG.RealiserContract2Cat",
    "LogOS.LT.LOG.RealiserFlow2Cat",
    "LogOS.LT.LOG.RealiserDecode2Cat",
    "LogOS.LT.LOG.EncodePort2CatG",
    "LogOS.LT.LOG.QuotePort2CatG",
    "LogOS.LT.LOG.QuotePort2CatG.Displayed",
    "LogOS.LT.LOG.FlowContract2CatG",
    "LogOS.LT.LOG.BulkBoundary2CatG",
    "LogOS.LT.LOG.BulkBoundaryContract2CatG",
    "LogOS.API.Ports.LTDecorationsLOGG",
    "LogOS.API.Ports.UniversalityLOGG",
    "LogOS.Ports.Universality.BudgetBus2CatG",
    "LogOS.Ports.Universality.FlowBudget2CatG",
}

SCAN_DIRS = [
    ROOT / "LogOS",
    ROOT / "docs" / "AI" / "Spec",
]


def lane_for(rel: str) -> str:
    if rel.startswith("LogOS/Apps/"):
        return "integration"
    return "canonical"


hits: dict[str, list[tuple[str, int, str]]] = {
    "canonical": [],
    "integration": [],
}

for scan_dir in SCAN_DIRS:
    if not scan_dir.exists():
        continue
    for path in sorted(scan_dir.rglob("*")):
        if path.suffix not in {".agda", ".md"}:
            continue
        if "_build" in path.parts:
            continue
        rel = path.relative_to(ROOT).as_posix()
        lane = lane_for(rel)
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for name in sorted(LEGACY_MODULES):
                if re.search(rf"\b{re.escape(name)}\b", line):
                    hits[lane].append((rel, i, name))
            for name in sorted(LEGACY_IDENTIFIERS):
                if re.search(rf"\b{re.escape(name)}\b", line):
                    hits[lane].append((rel, i, name))

status = (
    "Retired legacy names are absent from the canonical lane."
    if not hits["canonical"]
    else "Canonical lane still mentions retired legacy names."
)

with OUT.open("w", encoding="utf-8") as f:
    f.write("<!--\n")
    f.write("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI\n")
    f.write("Copyright (C) 2026 AI.IMPACT GmbH\n")
    f.write("SPDX-License-Identifier: GPL-3.0-only\n")
    f.write("-->\n\n")
    f.write("# Architecture Clarity Index (Generated)\n\n")
    f.write("Generated by `scripts/gen/write_architecture_clarity_index.sh`.\n\n")
    f.write("## Status\n\n")
    f.write(f"- {status}\n")
    f.write("- CI note: retired legacy names are hard-failed in canonical surfaces by `canonical-legacy-free-check`.\n\n")

    f.write("## Module Map\n\n")
    f.write("| Legacy module | Canonical module |\n")
    f.write("| --- | --- |\n")
    for old, new in MODULE_MAP:
        f.write(f"| `{old}` | `{new}` |\n")

    f.write("\n## Identifier Map\n\n")
    f.write("| Legacy name | Canonical name |\n")
    f.write("| --- | --- |\n")
    for old, new in IDENTIFIER_MAP:
        f.write(f"| `{old}` | `{new}` |\n")

    f.write("\n## Retired Legacy Module Paths\n\n")
    for old, _ in MODULE_MAP:
        f.write(f"- `{old}`\n")

    def write_hits(title: str, lane: str) -> None:
        lane_hits = hits[lane]
        f.write(f"\n## {title}\n\n")
        if lane_hits:
            f.write(f"- count: `{len(lane_hits)}`\n")
            for rel, line, name in lane_hits[:200]:
                f.write(f"- `{rel}` (line {line}): `{name}`\n")
            if len(lane_hits) > 200:
                f.write(f"- `... {len(lane_hits) - 200} more`\n")
        else:
            f.write("- none\n")

    write_hits("Canonical Lane Legacy Occurrences", "canonical")
    write_hits("Integration Lane Legacy Occurrences", "integration")

try:
    shown = str(OUT.relative_to(ROOT))
except ValueError:
    shown = str(OUT)
print(f"write-architecture-clarity-index: wrote {shown}")
PY
