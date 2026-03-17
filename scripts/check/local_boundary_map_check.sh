#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Locality boundary maps (`map∂`) must be pointwise/canonical (identity or pointwise map combinators).
# - Non-pointwise meaning changes must be quarantined (`LogOS/Ports/Quarantine/**`) or explicitly bridged.

set -euo pipefail

CHECK_NAME="local-boundary-map-check"
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

MAP_FIELD_RE = re.compile(r"\bmap∂\b\s*=\s*(.+?)\s*(?:--.*)?$")

# Gate only files that explicitly opt into the locality boundary vocabulary.
LOCALITY_MARKER_RE = re.compile(r"\b(LocalBoundary|DependentLocalBoundary)\b")

# Quarantine escapes: meaning-changing / non-pointwise translations must live here.
SKIP_PREFIXES = (
    "LogOS/Ports/Quarantine/",
    "LogOS/Ports/Bridges/",
)

# Allowed pointwise/canonical forms for boundary maps.
ALLOWED_SUBSTRINGS = (
    "pointwiseMap",
    "pointwiseEndoMap",
)

IDENTITY_LAM_RE = re.compile(r"^λ\s*([A-Za-z0-9_']+)\s*→\s*\(?\s*\\1\s*\)?\b")


def skip_file(rel: str) -> bool:
    return any(rel.startswith(p) for p in SKIP_PREFIXES)


def allowed_rhs(rhs: str) -> bool:
    rhs = rhs.strip()
    if any(s in rhs for s in ALLOWED_SUBSTRINGS):
        return True
    if IDENTITY_LAM_RE.match(rhs):
        return True
    return False


def main() -> int:
    if not LOGOS_DIR.is_dir():
        print("local-boundary-map-check: OK (no LogOS directory found)")
        return 0

    violations: list[str] = []

    for path in sorted(LOGOS_DIR.rglob("*.agda")):
        if "_build" in path.parts:
            continue

        rel = path.relative_to(ROOT).as_posix()
        if skip_file(rel):
            continue

        text = path.read_text(encoding="utf-8")
        if not LOCALITY_MARKER_RE.search(text):
            continue

        for i, line in enumerate(text.splitlines(), start=1):
            m = MAP_FIELD_RE.search(line)
            if not m:
                continue
            rhs = m.group(1)
            if not allowed_rhs(rhs):
                violations.append(f"{rel}:{i}: non-pointwise map∂ in locality module: {rhs.strip()}")

    if violations:
        print("local-boundary-map-check: FAIL", file=sys.stderr)
        print(
            "Policy: in locality-facing modules, boundary maps (`map∂`) must be pointwise/canonical",
            file=sys.stderr,
        )
        print(
            "(identity or pointwiseMap/pointwiseEndoMap variants). Non-local meaning changes must be",
            file=sys.stderr,
        )
        print(
            "quarantined under LogOS/Ports/Quarantine or explicitly bridged via LogOS/Ports/Bridges.",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  - {v}", file=sys.stderr)
        return 1

    print("local-boundary-map-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
