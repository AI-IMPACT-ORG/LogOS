#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

CHECK_NAME="layer-order-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"
# shellcheck source=scripts/lib/layers.sh
source "${SCRIPT_DIR}/lib/layers.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

LIB_ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
ALLOWLIST="${SCRIPT_DIR}/layer_order_allowlist.txt"

cd "${LIB_ROOT}"

check_require_cmd "${CHECK_NAME}" python3

# Policy: import layering follows docs/Core/Architecture/Diagram.lagda.md and the shared
# layer order in scripts/lib/layers.sh.
#
# Higher layers may import lower layers; lower layers must not import higher
# layers.

LAYERS_CSV="$(layers_csv)"

violations="$(
  LAYERS_CSV="${LAYERS_CSV}" python3 - <<'PY'
from __future__ import annotations

import os
import pathlib
import re

ROOT = pathlib.Path(".").resolve()

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)")

LAYERS = [layer for layer in os.environ.get("LAYERS_CSV", "").split(",") if layer]
LAYER: dict[str, int] = {layer: i for i, layer in enumerate(LAYERS)}


def category(mod: str) -> str:
  parts = mod.split(".")
  if len(parts) < 2 or parts[0] != "LogOS":
    return parts[0]
  return parts[1]


def main() -> int:
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
    src_path = path.relative_to(ROOT).as_posix()
    if src_cat not in LAYER:
      out.add(
        f"{src_path}: unknown LogOS category '{src_cat}' (update scripts/lib/layers.sh)"
      )
      continue
    src_layer = LAYER[src_cat]

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

tmp_allowlist="$(mktemp)"
trap 'rm -f "${tmp_allowlist}"' RETURN
grep -Ev '^[[:space:]]*(#|$)' "${ALLOWLIST}" >"${tmp_allowlist}" || true

remaining="$(printf "%s\n" "${violations}" | grep -v -F -f "${tmp_allowlist}" || true)"
if [[ -n "${remaining}" ]]; then
  die $'layering violations (see docs/Core/Architecture/Diagram.lagda.md):\n'"${remaining}"
fi

echo "layer-order-check: OK (allowlisted hits present)"
