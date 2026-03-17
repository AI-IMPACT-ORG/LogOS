#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="theorems-catalog-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

# Policy:
# - Every theorem module under `LogOS/LT/Theorems/**` must be explicitly catalogued by a public re-export in:
#   - `LogOS/API/Theorems/Core.agda`
#   - `LogOS/API/Theorems/Strictification.agda`
# - Exception: files ending in `*Impl.agda` are treated as internal packaging modules.
# - `Cone` and `MinimalModelProgram` are no longer valid theorem catalogs.

python3 - <<'PY'
from __future__ import annotations

import pathlib
import re
import sys

CHECK_NAME = "theorems-catalog-check"
ROOT = pathlib.Path(".").resolve()
THEOREMS_DIR = ROOT / "LogOS" / "LT" / "Theorems"
CATALOGS = [
    ROOT / "LogOS" / "API" / "Theorems" / "Core.agda",
    ROOT / "LogOS" / "API" / "Theorems" / "Strictification.agda",
]
IMPORT_RE = re.compile(r"^\s*open\s+import\s+([A-Za-z0-9_.']+)\b")
FORBIDDEN_CATALOG_MODULES = {
    "LogOS.LT.Theorems.Cone",
    "LogOS.LT.Theorems.MinimalModelProgram",
    "LogOS.LT.Theorems.QuoteConeMMP",
    "LogOS.LT.Theorems.QuoteConeMMP.PreQuotePort",
    "LogOS.LT.Theorems.QuoteConeMMP.QuoteStable",
}
INTERNAL_PREFIXES = (
    "LogOS.LT.Theorems.QuoteConeMMP",
    "LogOS.LT.Theorems.QuoteConeMMP.",
)


def module_from_path(path: pathlib.Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


if not THEOREMS_DIR.is_dir():
    print(f"{CHECK_NAME}: FAIL", file=sys.stderr)
    print("  - missing directory: LogOS/LT/Theorems/", file=sys.stderr)
    raise SystemExit(1)

for catalog in CATALOGS:
    if not catalog.is_file():
        print(f"{CHECK_NAME}: FAIL", file=sys.stderr)
        print(f"  - missing catalog file: {catalog.relative_to(ROOT).as_posix()}", file=sys.stderr)
        raise SystemExit(1)

theorem_modules: list[str] = []
for path in sorted(THEOREMS_DIR.rglob("*.agda")):
    if "_build" in path.parts or path.name.endswith("Impl.agda"):
        continue
    module_name = module_from_path(path)
    if any(module_name == prefix or module_name.startswith(prefix) for prefix in INTERNAL_PREFIXES):
        continue
    theorem_modules.append(module_name)

catalog_imports: set[str] = set()
violations: list[str] = []

for catalog in CATALOGS:
    rel = catalog.relative_to(ROOT).as_posix()
    for i, line in enumerate(catalog.read_text(encoding="utf-8").splitlines(), start=1):
        m = IMPORT_RE.match(line)
        if not m:
            continue
        mod = m.group(1)
        if mod in FORBIDDEN_CATALOG_MODULES:
            violations.append(f"{rel}:{i}: forbidden theorem catalog import {mod}")
        if mod.startswith("LogOS.LT.Theorems."):
            catalog_imports.add(mod)

missing = sorted(m for m in theorem_modules if m not in catalog_imports)
extra = sorted(m for m in catalog_imports.difference(theorem_modules))

if missing or extra or violations:
    print(f"{CHECK_NAME}: FAIL", file=sys.stderr)
    if missing:
        print("  - missing re-exports in LogOS/API/Theorems/{Core,Strictification}.agda:", file=sys.stderr)
        for m in missing:
            print(f"    * {m}", file=sys.stderr)
    if extra:
        print("  - catalog re-exports without a corresponding file under LogOS/LT/Theorems/**:", file=sys.stderr)
        for m in extra:
            print(f"    * {m}", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print(f"{CHECK_NAME}: OK")
PY
