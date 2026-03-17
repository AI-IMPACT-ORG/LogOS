#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `LogOS/API/**` is a curated surface.
# - It may only import from `LogOS.Prelude`, `LogOS.Syntax`, `LogOS.LT`,
#   `LogOS.Ports`, and `LogOS.API`.
# - Default API files must not import explicit strictification lanes.

set -euo pipefail

CHECK_NAME="api-purity-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(".").resolve()
API_DIR = ROOT / "LogOS" / "API"

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")

ALLOWED_PREFIXES = (
    "LogOS.Prelude",
    "LogOS.Syntax",
    "LogOS.LT",
    "LogOS.Ports",
    "LogOS.API",
)

STRICT_API_FILES = {
    "LogOS/API/Strictification.agda",
    "LogOS/API/Theorems/Strictification.agda",
    "LogOS/API/Ports/LTStrictificationLOG.agda",
}

STRICT_IMPORT_PATTERNS = (
    "LogOS.API.Strictification",
    "LogOS.API.Theorems.Strictification",
    "LogOS.API.Ports.LTStrictificationLOG",
    "LogOS.LT.Strictification.",
    "LogOS.LT.Hom.Strictification",
    "LogOS.LT.TypeTheory.Strictification",
    "LogOS.LT.Theorems.ArchitecturalNormalFormStrictification",
    "LogOS.LT.Discipline.ArchitectureImplementationLaw.Strictification",
    "LogOS.LT.Ports.PortSigStrictification",
    "LogOS.LT.Ports.PortStack.ClassicalLimit",
    "LogOS.LT.Ports.PortStack.Raw",
    "LogOS.Ports.ClassicalLimit",
)

STRICT_TOKENS = (
    "KernelHom≡",
    "StrictKernelHom",
    "decode-mapCode≡",
    "Tm≡",
    "strictifyDisplayed",
    "strictifyStack",
    "toFacadeHom-fromFacadeHom≡id",
    "fromFacadeHom-toFacadeHom≡id",
)


def allowed(mod: str) -> bool:
    return any(mod == p or mod.startswith(p + ".") for p in ALLOWED_PREFIXES)


def is_quarantined_import(mod: str) -> bool:
    return any(mod == p or mod.startswith(p) for p in STRICT_IMPORT_PATTERNS)


bad: list[str] = []

for path in sorted(API_DIR.rglob("*.agda")):
    if "_build" in path.parts:
        continue
    rel = path.relative_to(ROOT).as_posix()
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    for forbidden in ("Reachability-only import", "CI policy gates"):
        if forbidden in text:
            bad.append(f"{rel}: forbidden CI/plumbing marker in curated API surface: {forbidden!r}")

    is_strict_api_file = rel in STRICT_API_FILES

    for token in STRICT_TOKENS:
        if token in text and not is_strict_api_file:
            bad.append(f"{rel}: strict/equality-only token leaked into default API surface: {token}")

    for i, line in enumerate(lines, start=1):
        m = IMPORT_RE.match(line)
        if not m:
            continue
        mod = m.group(1)
        if not mod.startswith("LogOS."):
            bad.append(f"{rel}:{i}: forbidden non-LogOS import in API: {mod}")
            continue
        if not allowed(mod):
            bad.append(f"{rel}:{i}: API import outside allowed layers (Prelude/Syntax/LT/Ports/API): {mod}")
            continue
        if not is_strict_api_file and is_quarantined_import(mod):
            bad.append(f"{rel}:{i}: default API imports quarantined strict/equality surface: {mod}")

if bad:
    print("api-purity-check: FAIL", file=sys.stderr)
    for item in bad:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("api-purity-check: OK")
PY
