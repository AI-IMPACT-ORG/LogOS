#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "stable-surface-no-banned-transitive-imports-check: $*" >&2
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

import os
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
POSTULATE_RE = re.compile(r"^\s*postulate(\s|$)", re.MULTILINE)


def read_imports_agda(path: pathlib.Path) -> list[str]:
  out: list[str] = []
  for line in path.read_text(encoding="utf-8").splitlines():
    match = IMPORT_RE.match(line)
    if match:
      out.append(match.group(1))
  return out


def read_allowlist(path: pathlib.Path) -> dict[str, set[str]]:
  allowed: dict[str, set[str]] = defaultdict(set)
  if not path.exists():
    raise FileNotFoundError(path)
  invalid: list[str] = []
  for line in path.read_text(encoding="utf-8").splitlines():
    raw = line.rstrip("\n")
    stripped = raw.strip()
    if not stripped:
      continue
    if stripped.startswith("#"):
      continue

    main, sep, comment = raw.partition("#")
    main = main.strip()
    comment = comment.strip()
    if not main:
      continue
    if "JUSTIFICATION:" not in comment:
      invalid.append(raw)
      continue

    parts = main.split()
    if len(parts) != 2:
      invalid.append(raw)
      continue
    root, rule = parts[0], parts[1]
    allowed[root].add(rule)
  if invalid:
    raise ValueError(
      "invalid allowlist entries (each entry line must include an inline `# JUSTIFICATION: ...` comment):\n"
      + "\n".join(f"  {line}" for line in invalid)
    )
  return allowed


def is_allowed(allow: dict[str, set[str]], root: str, prefix: str) -> bool:
  if root not in allow:
    return False
  return prefix in allow[root]


def find_first_banned_path(
  *,
  root: str,
  edges: dict[str, set[str]],
  banned_prefixes: list[str],
  banned_segments: list[str],
  postulate_modules: set[str],
  allow: dict[str, set[str]],
) -> tuple[str, list[str], str] | None:
  parent: dict[str, str | None] = {root: None}
  queue: deque[str] = deque([root])

  while queue:
    mod = queue.popleft()
    for prefix in banned_prefixes:
      if mod.startswith(prefix) and not is_allowed(allow, root, prefix):
        # Reconstruct witness path.
        path: list[str] = []
        cur: str | None = mod
        while cur is not None:
          path.append(cur)
          cur = parent[cur]
        path.reverse()
        return (root, path, prefix)

    if mod in postulate_modules and not is_allowed(allow, root, "POSTULATE"):
      path: list[str] = []
      cur: str | None = mod
      while cur is not None:
        path.append(cur)
        cur = parent[cur]
      path.reverse()
      return (root, path, "POSTULATE")

    # Segment bans: ban *any* module whose name contains a segment token.
    # We match on ".<mod>." so segment strings can be written naturally
    # (e.g. ".Experimental."), without edge cases at the start/end.
    mod_dot = f".{mod}."
    for seg in banned_segments:
      if seg in mod_dot and not is_allowed(allow, root, seg):
        path: list[str] = []
        cur: str | None = mod
        while cur is not None:
          path.append(cur)
          cur = parent[cur]
        path.reverse()
        return (root, path, seg)

    for dep in sorted(edges.get(mod, ())):
      if dep in parent:
        continue
      parent[dep] = mod
      queue.append(dep)

  return None


def main() -> int:
  banned_prefixes = [
    "LogOS.Theorems.Meta.Assumptions.",
    "LogOS.Domain.",
  ]

  # Segment bans: stable roots must not depend (even transitively) on these.
  # Keep these short and structural: they match any module name segment.
  banned_segments = [".Experimental."]

  allowlist_file = pathlib.Path("scripts/stable_surface_transitive_allowlist.txt")
  try:
    allow = read_allowlist(allowlist_file)
  except Exception as e:
    print(
      f"stable-surface-no-banned-transitive-imports-check: invalid allowlist file {allowlist_file}: {e}",
      file=sys.stderr,
    )
    return 1

  agda_files: list[pathlib.Path] = []
  for base in ("LogOS", "Tests", "Examples"):
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

  postulate_modules: set[str] = set()
  for mod, path in modules.items():
    try:
      txt = path.read_text(encoding="utf-8")
    except OSError:
      continue
    if POSTULATE_RE.search(txt):
      postulate_modules.add(mod)

  stable_roots: set[str] = set()

  core_surfaces = (
    "LogOS/Kernel/Surface.agda",
    "LogOS/Ports/Surface.agda",
    "LogOS/Adapters/Surface.agda",
    "LogOS/Theorems/Surface.agda",
  )
  for rel in core_surfaces:
    p = ROOT / rel
    if p.exists():
      stable_roots.add(module_from_path(p))

  api_dir = ROOT / "LogOS" / "API"
  if api_dir.is_dir():
    for path in api_dir.glob("*.agda"):
      stable_roots.add(module_from_path(path))

  PACKTRUST_STABLE_RE = re.compile(
    r"^\s*packTrust\s*=\s*record\s*\{\s*level\s*=\s*stable\s*\}",
    re.MULTILINE,
  )

  stable_pack_dirs: list[pathlib.Path] = []
  for allfile in (ROOT / "LogOS" / "Packs").rglob("All.agda"):
    try:
      txt = allfile.read_text(encoding="utf-8")
    except OSError:
      continue
    if PACKTRUST_STABLE_RE.search(txt):
      stable_pack_dirs.append(allfile.parent)

  for root_dir in stable_pack_dirs:
    surface = root_dir / "Surface.agda"
    if surface.exists():
      stable_roots.add(module_from_path(surface))

  violations: list[tuple[str, list[str], str]] = []
  for root in sorted(stable_roots):
    if root not in modules:
      continue
    hit = find_first_banned_path(
      root=root,
      edges=edges,
      banned_prefixes=banned_prefixes,
      banned_segments=banned_segments,
      postulate_modules=postulate_modules,
      allow=allow,
    )
    if hit is not None:
      violations.append(hit)

  if violations:
    print("stable-surface-no-banned-transitive-imports-check: found banned transitive imports in stable roots:", file=sys.stderr)
    for root, path, prefix in violations:
      print(f"\n- Root: {root}", file=sys.stderr)
      print(f"  Banned rule: {prefix}", file=sys.stderr)
      print("  Witness path:", file=sys.stderr)
      for p in path:
        print(f"    {p}", file=sys.stderr)
    print(
      "\nRule: stable roots must not reach banned prefixes transitively.\n"
      f"Allowlist file: {allowlist_file}\n"
      "Format: `RootModule BannedRule  # JUSTIFICATION: ...`.\n"
      "BannedRule can be a module prefix (e.g. `LogOS.Theorems.Meta.Assumptions.`) or a segment token (e.g. `.Experimental.`).\n"
      "Special rule: `POSTULATE` bans any transitive dependency on a postulate-bearing module.\n"
      "Note: `LogOS.Domain.*` is always banned transitively for stable roots.",
      file=sys.stderr,
    )
    return 1

  print("stable-surface-no-banned-transitive-imports-check: OK")
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
PY
