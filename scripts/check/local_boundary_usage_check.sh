#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - `LocalBoundary` is the canonical (dependent-first) locality boundary.
# - `DependentLocalBoundary` is the retired legacy spelling and must not appear.

set -euo pipefail

CHECK_NAME="local-boundary-usage-check"
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
LOGOS_DIR = ROOT / "LogOS"

DEPENDENT_BOUNDARY_RE = re.compile(r"\bDependentLocalBoundary\b")


def main() -> int:
    if not LOGOS_DIR.is_dir():
        print("local-boundary-usage-check: OK (no LogOS directory found)")
        return 0

    violations: list[str] = []

    for path in sorted(LOGOS_DIR.rglob("*.agda")):
        if "_build" in path.parts:
            continue

        rel = path.relative_to(ROOT).as_posix()

        text = path.read_text(encoding="utf-8")
        if not DEPENDENT_BOUNDARY_RE.search(text):
            continue

        violations.append(rel)

    if violations:
        print("local-boundary-usage-check: FAIL", file=sys.stderr)
        print(
            "Policy: `DependentLocalBoundary` is the retired legacy spelling and must not be used.",
            file=sys.stderr,
        )
        print("Violations:", file=sys.stderr)
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    print("local-boundary-usage-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
