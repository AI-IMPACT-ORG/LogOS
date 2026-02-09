#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "doc-module-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

command -v python3 >/dev/null 2>&1 || die "python3 is required for this check"

python3 - <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(".").resolve()

ROOT_PREFIXES = (
    "LogOS/",
    "Tests/",
    "Examples/",
    "docs/",
    "scripts/",
    ".github/",
)

FENCE_RE = re.compile(r"^\s*```")
CODE_SPAN_RE = re.compile(r"`([^`]+)`")
LINK_DEST_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
REF_DEF_RE = re.compile(r"^\s*\[[^\]]+\]:\s*(\S+)")

MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_.]+)\b")


def iter_docs() -> list[Path]:
    docs: list[Path] = []
    for fixed in ("README.md", "CONTRIBUTING.md"):
        p = ROOT / fixed
        if p.is_file():
            docs.append(p)

    docs_dir = ROOT / "docs"
    if docs_dir.is_dir():
        for p in docs_dir.rglob("*"):
            if "_build" in p.parts:
                continue
            if p.suffix == ".md" or p.name.endswith(".lagda.md"):
                if p.is_file():
                    docs.append(p)

    logos_dir = ROOT / "LogOS"
    if logos_dir.is_dir():
        for p in logos_dir.rglob("*.md"):
            if "_build" in p.parts:
                continue
            if p.is_file():
                docs.append(p)

    return sorted({p.resolve() for p in docs})


def strip_fenced_blocks(text: str) -> str:
    out: list[str] = []
    inside = False
    for line in text.splitlines():
        if FENCE_RE.match(line):
            inside = not inside
            continue
        if not inside:
            out.append(line)
    return "\n".join(out)


def normalize_candidate(raw: str) -> str | None:
    s = raw.strip()
    if not s:
        return None
    if s.startswith("<") and s.endswith(">") and len(s) >= 2:
        s = s[1:-1].strip()
    if re.search(r"\s", s):
        s = s.split()[0]
    if s.startswith("#"):
        return None
    parsed = urlparse(s)
    if parsed.scheme and parsed.scheme.lower() in {"http", "https", "mailto", "ftp", "doi"}:
        return None
    if "#" in s:
        s = s.split("#", 1)[0]
    m = re.match(r"^(.*?)(?::(\d+)(?::(\d+))?)$", s)
    if m:
        path_part = m.group(1)
        if re.search(r"[/.]", path_part):
            s = path_part
    s = s.rstrip(".,;")
    return s or None


def resolve_repo_path(*, doc: Path, ref: str) -> Path:
    if ref.startswith("/"):
        return (ROOT / ref.lstrip("/")).resolve()
    if ref.startswith(ROOT_PREFIXES):
        return (ROOT / ref).resolve()
    return (doc.parent / ref).resolve()


def expected_module_for(path: Path) -> str:
    rel = path.relative_to(ROOT).as_posix()
    if rel.endswith(".lagda.md"):
        rel = rel[: -len(".lagda.md")]
    elif rel.endswith(".agda"):
        rel = rel[: -len(".agda")]
    return rel.replace("/", ".")


def actual_module_in_file(path: Path) -> str | None:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    for line in lines:
        m = MODULE_RE.match(line)
        if m:
            return m.group(1)
    return None


def main() -> int:
    docs = iter_docs()
    if not docs:
        print("doc-module-check: no markdown files found", file=sys.stderr)
        return 1

    mismatches: list[str] = []

    for doc in docs:
        try:
            text = doc.read_text(encoding="utf-8")
        except OSError as e:
            mismatches.append(f"{doc.relative_to(ROOT)}: cannot read: {e}")
            continue

        stripped = strip_fenced_blocks(text)

        refs: list[str] = []
        refs.extend(CODE_SPAN_RE.findall(stripped))
        refs.extend(LINK_DEST_RE.findall(stripped))
        for line in stripped.splitlines():
            m = REF_DEF_RE.match(line)
            if m:
                refs.append(m.group(1))

        for raw in refs:
            ref = normalize_candidate(raw)
            if ref is None:
                continue
            if re.search(r"\s", ref):
                continue
            if not (ref.endswith(".agda") or ref.endswith(".lagda.md")):
                continue

            path = resolve_repo_path(doc=doc, ref=ref)
            try:
                path_rel = path.relative_to(ROOT)
            except ValueError:
                mismatches.append(f"{doc.relative_to(ROOT)}: escapes repo root: {raw!r}")
                continue

            if not (ROOT / path_rel).exists():
                # Let doc-reference-check report missing paths; here we focus on module headers.
                continue

            expected = expected_module_for(ROOT / path_rel)
            actual = actual_module_in_file(ROOT / path_rel)
            if actual is None:
                mismatches.append(f"{doc.relative_to(ROOT)}: {ref!r}: cannot find module declaration")
                continue
            if expected != actual:
                mismatches.append(
                    f"{doc.relative_to(ROOT)}: {ref!r}: expected module {expected}, found {actual}"
                )

    if mismatches:
        print("doc-module-check: Agda module-name mismatches for referenced files:", file=sys.stderr)
        for item in mismatches:
            print(f"  - {item}", file=sys.stderr)
        return 1

    print("doc-module-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY

