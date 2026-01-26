#!/usr/bin/env bash
# LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "reachability-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${LIB_ROOT}"

if ! command -v python3 >/dev/null 2>&1; then
  die "python3 is required for this check"
fi

python3 - <<'PY'
from __future__ import annotations

import pathlib
import re
import sys
from collections import defaultdict, deque

ROOT = pathlib.Path(".").resolve()


def module_from_path(path: pathlib.Path) -> str:
  rel = path.relative_to(ROOT)
  if rel.suffix != ".agda":
    raise ValueError(f"unexpected suffix: {rel}")
  return ".".join(rel.with_suffix("").parts)


IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)")


def read_imports_agda(path: pathlib.Path) -> list[str]:
  out: list[str] = []
  for line in path.read_text(encoding="utf-8").splitlines():
    match = IMPORT_RE.match(line)
    if match:
      out.append(match.group(1))
  return out


def extract_docs_agda_blocks(path: pathlib.Path) -> list[str]:
  lines = path.read_text(encoding="utf-8").splitlines()
  inside = False
  out: list[str] = []
  for line in lines:
    if re.match(r"^\s*```\s*agda\s*$", line):
      inside = True
      continue
    if re.match(r"^\s*```\s*$", line) and inside:
      inside = False
      continue
    if inside:
      out.append(line)
  return out


def read_imports_docs(path: pathlib.Path) -> list[str]:
  out: list[str] = []
  for line in extract_docs_agda_blocks(path):
    match = IMPORT_RE.match(line)
    if match:
      out.append(match.group(1))
  return out


def is_core_path(path: pathlib.Path) -> bool:
  rel = path.relative_to(ROOT).as_posix()
  return rel.startswith("LogOS/") and not rel.startswith("LogOS/Domain/")


def main() -> int:
  agda_files: list[pathlib.Path] = []
  for base in ("LogOS", "Tests", "Examples", "docs"):
    base_path = ROOT / base
    if not base_path.is_dir():
      continue
    agda_files.extend(p for p in base_path.rglob("*.agda") if "_build" not in p.parts)

  modules: dict[str, pathlib.Path] = {}
  for path in agda_files:
    mod = module_from_path(path)
    modules[mod] = path

  edges: dict[str, set[str]] = defaultdict(set)
  for mod, path in modules.items():
    for dep in read_imports_agda(path):
      if dep in modules:
        edges[mod].add(dep)

  roots: set[str] = set()

  # Curated roots: tests + API + pack surfaces + examples.
  tests_all = ROOT / "Tests" / "All.agda"
  if tests_all.exists():
    roots.add(module_from_path(tests_all))

  for path in (ROOT / "LogOS" / "API").glob("*.agda"):
    roots.add(module_from_path(path))

  for path in (ROOT / "LogOS" / "Packs").rglob("Surface.agda"):
    roots.add(module_from_path(path))

  # Domain umbrellas count as roots: they are the intended “entrypoints” for
  # each domain development. This keeps Domain modules from silently becoming
  # code islands: a new Domain module should be reachable via some `.../All.agda`
  # (or via tests/packs/docs) or the check will fail.
  for path in (ROOT / "LogOS" / "Domain").rglob("All.agda"):
    roots.add(module_from_path(path))

  for path in (ROOT / "Examples").glob("*.agda"):
    roots.add(module_from_path(path))

  # Docs also count as roots: anything imported from literate Agda blocks is anchored.
  for doc in (ROOT / "docs").rglob("*.lagda.md"):
    for dep in read_imports_docs(doc):
      if dep in modules:
        roots.add(dep)

  reachable: set[str] = set()
  queue: deque[str] = deque(sorted(roots))

  while queue:
    mod = queue.popleft()
    if mod in reachable:
      continue
    reachable.add(mod)
    for dep in edges.get(mod, ()):
      if dep not in reachable:
        queue.append(dep)

  unreachable_core: list[str] = []
  unreachable_domain: list[str] = []

  for mod, path in modules.items():
    if mod in reachable:
      continue
    rel = path.relative_to(ROOT).as_posix()
    if rel.startswith("LogOS/Domain/"):
      unreachable_domain.append(mod)
    elif is_core_path(path):
      unreachable_core.append(mod)

  if unreachable_core:
    print("reachability-check: unreachable core modules:", file=sys.stderr)
    for mod in sorted(unreachable_core):
      print(f"  - {mod}", file=sys.stderr)
    return 1

  if unreachable_domain:
    print("reachability-check: unreachable LogOS.Domain modules:", file=sys.stderr)
    for mod in sorted(unreachable_domain):
      print(f"  - {mod}", file=sys.stderr)
    return 1

  print("reachability-check: OK")
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
PY
