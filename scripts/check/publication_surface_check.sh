#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Publication tiers are explicit, not inferred from directory names.
# - Published entries must be curated surfaces with a navigator (`README.md` or a local `All` entrypoint module for directories).
# - Archive and optional tooling subtrees must never be classified as published.

set -euo pipefail

CHECK_NAME="publication-surface-check"
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
MANIFEST = ROOT / "scripts" / "publication_surface.tsv"
FORBIDDEN_PUBLISHED_PREFIXES = ("Archive/", "tools/metamath/", "scripts/metamath/")

if not MANIFEST.is_file():
    print("publication-surface-check: FAIL", file=sys.stderr)
    print("  - missing manifest scripts/publication_surface.tsv", file=sys.stderr)
    raise SystemExit(1)

errors: list[str] = []
seen_paths: set[str] = set()

for i, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), start=1):
    line = raw.strip()
    if not line or line.startswith("#"):
        continue
    cols = [part.strip() for part in raw.split("\t")]
    if len(cols) != 4 or any(not col for col in cols):
        errors.append(f"scripts/publication_surface.tsv:{i}: expected <tier><TAB><kind><TAB><path><TAB><note>")
        continue
    tier, kind, rel, note = cols
    if tier not in {"published", "internal", "archive"}:
        errors.append(f"scripts/publication_surface.tsv:{i}: unknown tier {tier!r}")
    if kind not in {"dir", "file"}:
        errors.append(f"scripts/publication_surface.tsv:{i}: unknown kind {kind!r}")
    if rel in seen_paths:
        errors.append(f"scripts/publication_surface.tsv:{i}: duplicate path {rel}")
    seen_paths.add(rel)
    path = ROOT / rel
    if kind == "dir" and not path.is_dir():
        errors.append(f"scripts/publication_surface.tsv:{i}: expected directory {rel}")
    if kind == "file" and not path.is_file():
        errors.append(f"scripts/publication_surface.tsv:{i}: expected file {rel}")
    if tier == "published":
        if rel.startswith(FORBIDDEN_PUBLISHED_PREFIXES):
            errors.append(f"scripts/publication_surface.tsv:{i}: published path must not point into archive/tooling: {rel}")
        if kind == "dir":
            if not ((path / "README.md").is_file() or (path / "All.agda").is_file()):
                errors.append(f"{rel}: published directory needs README.md or All.agda navigator")

if errors:
    print("publication-surface-check: FAIL", file=sys.stderr)
    for item in errors:
        print(f"  - {item}", file=sys.stderr)
    raise SystemExit(1)

print("publication-surface-check: OK")
PY
