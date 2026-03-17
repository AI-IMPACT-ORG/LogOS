#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Curated literate docs must be discoverable from the generated docs inventory.
# - Every `docs/{Core,Results,Patterns,Interpretations}/**/*.lagda.md` file must be referenced from `docs/Generated/Docs_Index.md`.

set -euo pipefail

CHECK_NAME="curated-docs-index-coverage-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

INDEX="docs/Generated/Docs_Index.md"
[[ -f "${INDEX}" ]] || die "missing generated docs index: ${INDEX}"

python3 - <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(".").resolve()
INDEX = ROOT / "docs/Generated/Docs_Index.md"
INDEX_DIR = INDEX.parent.resolve()
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

refs: set[str] = set()
text = INDEX.read_text(encoding="utf-8")
for raw_dest in LINK_RE.findall(text):
    dest = raw_dest.strip()
    if not dest:
        continue
    if dest.startswith("<") and dest.endswith(">") and len(dest) >= 2:
        dest = dest[1:-1].strip()
    if "#" in dest:
        dest = dest.split("#", 1)[0]
    if not dest:
        continue
    cand = (INDEX_DIR / dest).resolve()
    try:
        refs.add(cand.relative_to(ROOT).as_posix())
    except ValueError:
        continue

expected: list[str] = []
for base in ("docs/Core", "docs/Results", "docs/Patterns", "docs/Interpretations"):
    for path in sorted((ROOT / base).rglob("*.lagda.md")):
        expected.append(path.relative_to(ROOT).as_posix())

missing = [path for path in expected if path not in refs]
if missing:
    print(
        "docs/Generated/Docs_Index.md is missing references to curated literate docs:",
        file=sys.stderr,
    )
    for path in missing:
        print(path, file=sys.stderr)
    print(
        "\nRule: every docs/{Core,Results,Patterns,Interpretations}/**/*.lagda.md file "
        "must be linked from docs/Generated/Docs_Index.md.",
        file=sys.stderr,
    )
    sys.exit(1)

print("curated-docs-index-coverage-check: OK")
PY
