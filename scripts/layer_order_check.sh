#!/usr/bin/env bash
# LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

die() {
  echo "layer-order-check: $*" >&2
  exit 1
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIB_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
ALLOWLIST="${SCRIPT_DIR}/layer_order_allowlist.txt"

cd "${LIB_ROOT}"

if ! command -v python3 >/dev/null 2>&1; then
  die "python3 is required for this check"
fi

# Policy: import layering follows the README architecture diagram.
#
# Higher layers may import lower layers; lower layers must not import higher layers.
#
# Layers (low → high):
#   0 Host
#   1 Prelude
#   2 Foundations (Base/Syntax/Algebra/Free)
#   3 Minimal
#   4 Kernel/QAdapters/Computation/Axioms/MetaLanguage
#   5 Boundary/Ports/Adapters/System
#   6 Theorems
#   7 Topic libraries (ZFC/UniversalIR/Universality/Complexity/InfoTheory/ObjectLogic)
#   8 Domain (experimental)
#   9 Packs (curated entrypoints)
#
# Note: `LogOS/API/**` is intentionally excluded from this check for now; API
# modules are curated import surfaces and are governed by other policy checks.

violations="$(
  python3 - <<'PY'
from __future__ import annotations

import pathlib
import re

ROOT = pathlib.Path(".").resolve()

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)")

LAYER: dict[str, int] = {
  "Host": 0,
  "Prelude": 1,
  "Base": 2,
  "Syntax": 2,
  "Algebra": 2,
  "Free": 2,
  "Minimal": 3,
  "Kernel": 4,
  "QAdapters": 4,
  "Computation": 4,
  "Axioms": 4,
  "MetaLanguage": 4,
  "Boundary": 5,
  "Ports": 5,
  "Adapters": 5,
  "System": 5,
  "Theorems": 6,
  "ZFC": 7,
  "UniversalIR": 7,
  "Universality": 7,
  "Complexity": 7,
  "InfoTheory": 7,
  "ObjectLogic": 7,
  "Domain": 8,
  "Packs": 9,
  # API intentionally excluded
}


def category(mod: str) -> str:
  parts = mod.split(".")
  if len(parts) < 2 or parts[0] != "LogOS":
    return parts[0]
  return parts[1]


def main() -> int:
  # Discover Agda modules under LogOS.
  agda_files = [
    p
    for p in (ROOT / "LogOS").rglob("*.agda")
    if "_build" not in p.parts
  ]
  modules: dict[str, pathlib.Path] = {}
  for path in agda_files:
    mod = ".".join(path.relative_to(ROOT).with_suffix("").parts)
    modules[mod] = path

  out: set[str] = set()

  for mod, path in modules.items():
    src_cat = category(mod)
    if src_cat not in LAYER:
      continue
    src_layer = LAYER[src_cat]
    src_path = path.relative_to(ROOT).as_posix()

    for line in path.read_text(encoding="utf-8").splitlines():
      match = IMPORT_RE.match(line)
      if not match:
        continue
      dep = match.group(1)
      if dep not in modules:
        continue
      dep_cat = category(dep)
      if dep_cat not in LAYER:
        continue
      dep_layer = LAYER[dep_cat]
      if src_layer < dep_layer:
        out.add(
          f"{src_path}: {src_cat}({src_layer}) imports {dep} [{dep_cat}({dep_layer})]"
        )

  for line in sorted(out):
    print(line)
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
PY
)"

if [[ -z "${violations}" ]]; then
  echo "layer-order-check: OK"
  exit 0
fi

if [[ ! -f "${ALLOWLIST}" ]]; then
  die $'allowlist missing (expected scripts/layer_order_allowlist.txt); violations:\n'"${violations}"
fi

remaining="$(printf "%s\n" "${violations}" | grep -v -F -f "${ALLOWLIST}" || true)"
if [[ -n "${remaining}" ]]; then
  die $'layering violations (see README architecture diagram):\n'"${remaining}"
fi

echo "layer-order-check: OK (allowlisted hits present)"

