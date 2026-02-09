#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "doc-reference-check: $*" >&2
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

EXTS = (
    ".agda",
    ".lagda.md",
    ".md",
    ".tex",
    ".sh",
    ".yml",
    ".yaml",
    ".json",
    ".agda-lib",
    ".cff",
)


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

    # Stable deterministic order + no duplicates.
    uniq = sorted({p.resolve() for p in docs})
    return uniq


FENCE_RE = re.compile(r"^\s*```")


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


CODE_SPAN_RE = re.compile(r"`([^`]+)`")

# Conservative link extraction:
# - inline: [text](dest)
# - images: ![alt](dest)
LINK_DEST_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

# Reference-style links: [id]: dest
REF_DEF_RE = re.compile(r"^\s*\[[^\]]+\]:\s*(\S+)")


def normalize_candidate(raw: str) -> str | None:
    s = raw.strip()
    if not s:
        return None

    # Markdown allows `<...>` around destinations.
    if s.startswith("<") and s.endswith(">") and len(s) >= 2:
        s = s[1:-1].strip()

    # Drop optional link title: (path "title") / (path 'title').
    if re.search(r"\s", s):
        s = s.split()[0]

    # Ignore URL-ish destinations and pure anchors.
    if s.startswith("#"):
        return None
    parsed = urlparse(s)
    if parsed.scheme and parsed.scheme.lower() in {"http", "https", "mailto", "ftp", "doi"}:
        return None

    # Drop fragment (`file#anchor`).
    if "#" in s:
        s = s.split("#", 1)[0]

    # Allow file references with `:line[:col]`.
    m = re.match(r"^(.*?)(?::(\d+)(?::(\d+))?)$", s)
    if m:
        path_part = m.group(1)
        # Only treat it as a line/col reference if the path part actually
        # looks like a path (avoid mis-parsing random `a:b` tokens).
        if re.search(r"[/.]", path_part):
            s = path_part

    # Small punctuation tolerance (mostly for prose like `docs/Foo.md,`).
    s = s.rstrip(".,;")

    return s or None


def looks_like_path(s: str) -> bool:
    if s.startswith(("/", "./", "../")):
        return True
    if s.startswith(ROOT_PREFIXES):
        return True
    return any(s.endswith(ext) for ext in EXTS)


def resolve_repo_path(*, doc: Path, ref: str) -> Path | None:
    # Root-relative markdown links (`/docs/...`) are treated as repo-root relative.
    if ref.startswith("/"):
        return (ROOT / ref.lstrip("/")).resolve()
    # Explicitly root-anchored prefixes.
    if ref.startswith(ROOT_PREFIXES):
        return (ROOT / ref).resolve()
    # Otherwise, resolve relative to the doc's directory.
    return (doc.parent / ref).resolve()


def check_candidate(*, doc: Path, raw: str, kind: str, missing: list[str]) -> None:
    ref = normalize_candidate(raw)
    if ref is None or not looks_like_path(ref):
        return
    if re.search(r"\s", ref):
        # Mirror the previous check: skip inline code containing whitespace.
        return

    # Light glob support: check that the non-glob prefix exists.
    if any(ch in ref for ch in "*{}"):
        prefix = ref
        prefix = prefix.split("*", 1)[0]
        prefix = prefix.split("{", 1)[0]
        prefix = prefix.split("}", 1)[0]
        if not prefix:
            return
        cand = resolve_repo_path(doc=doc, ref=prefix)
    else:
        cand = resolve_repo_path(doc=doc, ref=ref)

    if cand is None:
        return
    try:
        cand_rel = cand.relative_to(ROOT)
    except ValueError:
        missing.append(f"{doc.relative_to(ROOT)}: escapes repo root: {raw!r}")
        return

    if not (ROOT / cand_rel).exists():
        missing.append(f"{doc.relative_to(ROOT)}: missing reference: {raw!r}")


def main() -> int:
    docs = iter_docs()
    if not docs:
        print("doc-reference-check: no markdown files found", file=sys.stderr)
        return 1

    missing: list[str] = []

    for doc in docs:
        try:
            text = doc.read_text(encoding="utf-8")
        except OSError as e:
            missing.append(f"{doc.relative_to(ROOT)}: cannot read: {e}")
            continue

        stripped = strip_fenced_blocks(text)

        # Inline code spans.
        for span in CODE_SPAN_RE.findall(stripped):
            check_candidate(doc=doc, raw=span, kind="code", missing=missing)

        # Inline markdown link destinations.
        for dest in LINK_DEST_RE.findall(stripped):
            check_candidate(doc=doc, raw=dest, kind="link", missing=missing)

        # Reference-style definitions.
        for line in stripped.splitlines():
            m = REF_DEF_RE.match(line)
            if m:
                check_candidate(doc=doc, raw=m.group(1), kind="ref", missing=missing)

    if missing:
        print("doc-reference-check: missing referenced paths in markdown docs:", file=sys.stderr)
        for item in missing:
            print(f"  - {item}", file=sys.stderr)
        return 1

    print("doc-reference-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
