#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The documentation must present the canonical conceptual spine in order
#   (ConPreorder → View → Kernel → KernelHom → LOG → DisplayedThin2Cat → DecoratedThin2Cat),
#   so the library stays self-similar and discoverable.

set -euo pipefail

CHECK_NAME="spine-doc-contract-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import sys
from pathlib import Path

DOC = Path("docs/Core/Orientation/LogOS_Overview.lagda.md")
if not DOC.is_file():
    print(f"spine-doc-contract-check: missing doc: {DOC}", file=sys.stderr)
    sys.exit(1)

text = DOC.read_text(encoding="utf-8")

marker = "Conceptual spine (self-similar presentation)"
start = text.find(marker)
if start < 0:
    print("spine-doc-contract-check: FAIL", file=sys.stderr)
    print(f"missing marker heading: {marker}", file=sys.stderr)
    sys.exit(1)

spine_text = text[start:]

tokens = ["ConPreorder", "View", "Kernel", "KernelHom", "LOG", "DisplayedThin2Cat", "DecoratedThin2Cat"]

pos = -1
missing: list[str] = []
order_violation: list[str] = []

for t in tokens:
    needle = f"`{t}`"
    i = spine_text.find(needle)
    if i < 0:
        missing.append(t)
        continue
    if i <= pos:
        order_violation.append(t)
    pos = i

if missing:
    print("spine-doc-contract-check: FAIL", file=sys.stderr)
    print("missing spine tokens in docs/Core/Orientation/LogOS_Overview.lagda.md:", file=sys.stderr)
    for t in missing:
        print(f"  - {t}", file=sys.stderr)
    sys.exit(1)

if order_violation:
    print("spine-doc-contract-check: FAIL", file=sys.stderr)
    print("spine tokens appear out of order in docs/Core/Orientation/LogOS_Overview.lagda.md:", file=sys.stderr)
    for t in order_violation:
        print(f"  - {t}", file=sys.stderr)
    print("expected order:", file=sys.stderr)
    print("  " + " → ".join(tokens), file=sys.stderr)
    sys.exit(1)

print("spine-doc-contract-check: OK")
PY
