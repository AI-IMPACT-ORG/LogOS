#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Any `*2Cat.agda` module that defines a law-port via `LawDisplayed`/`LawDisplayedOn` must provide
#   an explicit `forget…` projection (unless it carries an explicit justification marker).
# - This keeps “data + law” ports usable and prevents unprojectable “sealed” constructions.

set -euo pipefail

CHECK_NAME="law-port-forgetfuls-doc-check"
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

files: list[Path] = []
log_dir = ROOT / "LogOS" / "LT" / "LOG"
ports_dir = ROOT / "LogOS" / "Ports"

if log_dir.is_dir():
    files += sorted(log_dir.glob("*2Cat.agda"))
if ports_dir.is_dir():
    files += sorted(ports_dir.rglob("*2Cat.agda"))

has_forget_def = re.compile(r"^\s*forget[A-Za-z0-9_']*\s*(?::|=)", re.M)

violations: list[str] = []
for p in files:
    text = p.read_text(encoding="utf-8")

    if "LawDisplayed" not in text and "LawDisplayedOn" not in text:
        continue

    if "LAW-PORT-NO-FORGETFUL-JUSTIFICATION:" in text:
        continue

    if not has_forget_def.search(text):
        violations.append(str(p.relative_to(ROOT)))

if violations:
    print("law-port-forgetfuls-doc-check: FAIL", file=sys.stderr)
    print("law-port modules missing an explicit `forget…` projection:", file=sys.stderr)
    for v in violations:
        print(f"  - {v}", file=sys.stderr)
    print("", file=sys.stderr)
    print("Fix: add a `forget…` definition, or add `LAW-PORT-NO-FORGETFUL-JUSTIFICATION:`.", file=sys.stderr)
    sys.exit(1)

print("law-port-forgetfuls-doc-check: OK")
PY

