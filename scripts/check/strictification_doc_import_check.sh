#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Literate docs are refinement-first by default.
# - Docs may import `*Strictification*` modules only when the doc file name
#   itself advertises that mode (`Strict`, `Extensional`, or `ClassicalLimit`),
#   except for the canonical LT spec import inventory.

set -euo pipefail

CHECK_NAME="strictification-doc-import-check"
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
DOCS = ROOT / "docs"
EXCLUDED = {
    ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md",
}
ALLOWED_TOKENS = ("Strict", "Extensional", "ClassicalLimit")
IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']*Strictification[A-Za-z0-9_.']*)\b")

violations: list[str] = []

for path in sorted(DOCS.rglob("*.lagda.md")):
    if path in EXCLUDED or "Generated" in path.parts:
        continue
    if any(token in path.name for token in ALLOWED_TOKENS):
        continue
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        m = IMPORT_RE.match(line)
        if m:
            rel = path.relative_to(ROOT).as_posix()
            violations.append(f"{rel}:{i}: {m.group(1)}")

if violations:
    print("strictification-doc-import-check: FAIL", file=sys.stderr)
    for item in violations:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("strictification-doc-import-check: OK")
PY
