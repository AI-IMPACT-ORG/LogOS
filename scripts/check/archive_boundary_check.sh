#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Historical material must not be treated as part of the live repository root.
# - The live repo root must not carry stale archive entrypoints such as `TEMP`
#   or `Archive.zip`.
# - If an in-repo archive subtree is present, its entrypoints must say that they
#   are historical and out of contract.

set -euo pipefail

CHECK_NAME="archive-boundary-check"
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

ROOT = Path(".").resolve()

ROOT_FORBIDDEN = [
    ROOT / "TEMP",
    ROOT / "Archive.zip",
]

errors: list[str] = []

for path in ROOT_FORBIDDEN:
    if path.exists():
        errors.append(f"historical artifact must not live at repo root: {path.relative_to(ROOT).as_posix()}")

if errors:
    print("archive-boundary-check: FAIL", file=sys.stderr)
    for item in errors:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("archive-boundary-check: OK")
PY
