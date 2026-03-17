#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Every `LogOS/LT/**` module must declare exactly one `-- SpecRef:` line.
# - `docs/Core/Spec/LogicalTransformers.lagda.md` must import every `LogOS.LT.*` module (sync guard).

set -euo pipefail

CHECK_NAME="spec-ref-check"
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
LT_ROOT = ROOT / "LogOS" / "LT"
DOC = ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md"

if not LT_ROOT.is_dir():
    print("spec-ref-check: missing LogOS/LT", file=sys.stderr)
    raise SystemExit(1)
if not DOC.is_file():
    print(f"spec-ref-check: missing {DOC.relative_to(ROOT).as_posix()}", file=sys.stderr)
    raise SystemExit(1)

errors: list[str] = []
modules: list[str] = []

for path in sorted(LT_ROOT.rglob("*.agda")):
    if "_build" in path.parts:
        continue

    rel = path.relative_to(ROOT)
    module_name = ".".join(rel.with_suffix("").parts)
    modules.append(module_name)

    text = path.read_text(encoding="utf-8")
    count = len(re.findall(r"^\s*--\s*SpecRef:\s*", text, flags=re.MULTILINE))
    if count != 1:
        errors.append(f"{rel}: expected exactly 1 SpecRef line, found {count}")

doc_text = DOC.read_text(encoding="utf-8")
imported = {
    m.group(1)
    for m in re.finditer(r"^\s*import\s+(LogOS\.LT(?:\.[A-Za-z0-9_']+)*)\s*$", doc_text, flags=re.MULTILINE)
}

missing_imports = [m for m in modules if m not in imported]
if missing_imports:
    errors.append(
        "docs/Core/Spec/LogicalTransformers.lagda.md: missing LogOS.LT imports:\n"
        + "\n".join(f"  - {m}" for m in missing_imports)
        + "\n\nTip: run `make spec-lt-imports` to regenerate the LT import block."
    )

if errors:
    print("spec-ref-check: violations:", file=sys.stderr)
    for e in errors:
        print(f"  - {e}", file=sys.stderr)
    raise SystemExit(1)

print("spec-ref-check: OK")
PY
