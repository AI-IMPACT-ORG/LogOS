#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Each current tool subproject under `tools/metamath/**` must declare purpose,
#   dependencies, a smoke command, and outputs.
# - The canonical smoke entrypoints live under `scripts/metamath/**`.

set -euo pipefail

CHECK_NAME="tooling-contract-check"
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

README_REQUIREMENTS = {
    ROOT / "tools" / "metamath" / "README.md": [
        "## Purpose",
        "## Dependencies",
        "## Smoke test",
        "## Outputs",
    ],
    ROOT / "tools" / "metamath" / "mmc" / "README.md": [
        "## Purpose",
        "## Dependencies",
        "## Smoke test",
        "## Outputs",
    ],
    ROOT / "tools" / "metamath" / "parse_mm" / "README.md": [
        "## Purpose",
        "## Dependencies",
        "## Smoke test",
        "## Outputs",
    ],
}

SMOKE_SCRIPTS = {
    ROOT / "scripts" / "metamath" / "mmc_smoke.sh": "scripts/metamath/testdata/mini.mm",
    ROOT / "scripts" / "metamath" / "parse_mm_smoke.sh": "scripts/metamath/testdata/mini.mm",
}

errors: list[str] = []

for path, markers in README_REQUIREMENTS.items():
    if not path.is_file():
        errors.append(f"missing tool README: {path.relative_to(ROOT).as_posix()}")
        continue
    text = path.read_text(encoding="utf-8")
    for marker in markers:
        if marker not in text:
            errors.append(f"{path.relative_to(ROOT).as_posix()}: missing required section {marker!r}")

for path, required_ref in SMOKE_SCRIPTS.items():
    if not path.is_file():
        errors.append(f"missing smoke script: {path.relative_to(ROOT).as_posix()}")
        continue
    text = path.read_text(encoding="utf-8")
    if required_ref not in text:
        errors.append(
            f"{path.relative_to(ROOT).as_posix()}: smoke script must reference {required_ref!r}"
        )

if errors:
    print("tooling-contract-check: FAIL", file=sys.stderr)
    for item in errors:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("tooling-contract-check: OK")
PY
