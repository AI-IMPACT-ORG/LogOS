#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

set -euo pipefail

python3 - <<'PY'
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(".").resolve()
DOC = ROOT / "docs" / "Core" / "Spec" / "LogicalTransformers.lagda.md"
LT_ROOT = ROOT / "LogOS" / "LT"

BEGIN = "-- LT-IMPORTS-BEGIN (generated)"
END = "-- LT-IMPORTS-END"

if not DOC.is_file():
  print(f"write_spec_lt_imports: missing {DOC}", file=sys.stderr)
  raise SystemExit(1)
if not LT_ROOT.is_dir():
  print(f"write_spec_lt_imports: missing {LT_ROOT}", file=sys.stderr)
  raise SystemExit(1)

modules: list[str] = []
for path in sorted(LT_ROOT.rglob("*.agda")):
  if "_build" in path.parts:
    continue
  rel = path.relative_to(ROOT)
  modules.append(".".join(rel.with_suffix("").parts))

generated = "\n".join(f"import {m}" for m in modules)
block = f"{BEGIN}\n{generated}\n{END}"

text = DOC.read_text(encoding="utf-8")
pattern = re.compile(rf"(?ms)^{re.escape(BEGIN)}\n.*?\n{re.escape(END)}$")

if not pattern.search(text):
  print(
    f"write_spec_lt_imports: missing LT import markers in {DOC.relative_to(ROOT).as_posix()}\n"
    f"Expected lines:\n  {BEGIN}\n  {END}",
    file=sys.stderr,
  )
  raise SystemExit(1)

new_text = pattern.sub(block, text)
if new_text != text:
  DOC.write_text(new_text, encoding="utf-8")
  print("write_spec_lt_imports: updated docs/Core/Spec/LogicalTransformers.lagda.md")
else:
  print("write_spec_lt_imports: no changes")
PY
