#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Meaning-changing constructions under `LogOS.Ports.Quarantine/**` may only be imported by Quarantine itself
#   and curated bridge modules.

set -euo pipefail

CHECK_NAME="quarantine-import-check"
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

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")

QUAR_PREFIX = "LogOS.Ports.Quarantine"
ALLOWED_IMPORTER_PREFIXES = (
    "LogOS/Ports/Quarantine/",
    "LogOS/Ports/Bridges/",
)


def allowed_importer(rel: str) -> bool:
    return any(rel.startswith(p) for p in ALLOWED_IMPORTER_PREFIXES)


def main() -> int:
    logos_dir = ROOT / "LogOS"
    if not logos_dir.is_dir():
        print("quarantine-import-check: OK (no LogOS directory found)")
        return 0

    violations: list[str] = []

    for path in sorted(logos_dir.rglob("*.agda")):
        if "_build" in path.parts:
            continue

        rel = path.relative_to(ROOT).as_posix()
        if allowed_importer(rel):
            continue

        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            dep = m.group(1)
            if dep == QUAR_PREFIX or dep.startswith(QUAR_PREFIX + "."):
                violations.append(f"{rel}:{i}: forbidden import of quarantined module: {dep}")

    if violations:
        print("quarantine-import-check: FAIL", file=sys.stderr)
        print(
            "Policy: quarantined meaning-changing constructions under LogOS.Ports.Quarantine",
            file=sys.stderr,
        )
        print(
            "may only be imported by Quarantine itself or curated Bridges modules.",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    print("quarantine-import-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
