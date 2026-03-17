#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - ZFC assumption/upgrade packs must be manifest-listed and called out in the
#   canonical assumptions ledger.
# - Derived-theorem upgrade entries additionally need an explicit claim-stamp
#   anchor in the ledger/docs story.

set -euo pipefail

CHECK_NAME="zfc-upgrade-discipline-check"
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
ZFC_DIR = ROOT / "LogOS" / "Apps" / "ZFC"
LEDGER = ROOT / "docs" / "Core" / "Meta" / "Assumptions_Ledger.md"
MANIFEST = ROOT / "scripts" / "zfc_upgrade_manifest.tsv"

RECORD_RE = re.compile(r"^\s*record\s+([A-Za-z0-9_]+(?:Assumptions|Ledger|Upgrade))\b")


def module_from_path(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    assert rel.endswith(".agda")
    return rel[:-5].replace("/", ".")


if not LEDGER.is_file():
    print(f"{LEDGER.relative_to(ROOT)}: missing assumptions ledger", file=sys.stderr)
    raise SystemExit(1)
if not MANIFEST.is_file():
    print(f"{MANIFEST.relative_to(ROOT)}: missing zfc upgrade manifest", file=sys.stderr)
    raise SystemExit(1)

ledger_text = LEDGER.read_text(encoding="utf-8")

manifest: dict[tuple[str, str], tuple[str, str, str]] = {}
for i, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    cols = raw.split("\t")
    if len(cols) != 5:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: expected 5 tab-separated columns", file=sys.stderr)
        raise SystemExit(1)
    kind, module_name, symbol, ledger_anchor, status = cols
    if kind not in {"assumption", "ledger", "upgrade-record", "upgrade-builder", "theorem-upgrade"}:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: invalid kind {kind!r}", file=sys.stderr)
        raise SystemExit(1)
    if status not in {"explicit-parameter", "derived-theorem"}:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: invalid status {status!r}", file=sys.stderr)
        raise SystemExit(1)
    key = (module_name, symbol)
    if key in manifest:
        print(f"{MANIFEST.relative_to(ROOT)}:{i}: duplicate manifest entry for {module_name}.{symbol}", file=sys.stderr)
        raise SystemExit(1)
    manifest[key] = (kind, ledger_anchor, status)

found: set[tuple[str, str]] = set()
violations: list[str] = []

for path in sorted(ZFC_DIR.rglob("*.agda")):
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        m = RECORD_RE.match(line)
        if not m:
            continue
        symbol = m.group(1)
        module_name = module_from_path(path)
        key = (module_name, symbol)
        found.add(key)
        if key not in manifest:
            violations.append(f"{path.relative_to(ROOT).as_posix()}:{i}: missing manifest coverage for {module_name}.{symbol}")
            continue
        _kind, ledger_anchor, status = manifest[key]
        if symbol not in ledger_text:
            violations.append(f"{LEDGER.relative_to(ROOT)}: missing ledger mention for {symbol}")
        if status == "derived-theorem" and ledger_anchor not in ledger_text:
            violations.append(f"{LEDGER.relative_to(ROOT)}: derived-theorem entry lacks declared claim-stamp anchor {ledger_anchor!r} for {symbol}")

for module_name, symbol in sorted(set(manifest) - found):
    violations.append(f"manifest entry does not correspond to a current ZFC record: {module_name}.{symbol}")

if violations:
    print("zfc-upgrade-discipline-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("zfc-upgrade-discipline-check: OK")
PY
