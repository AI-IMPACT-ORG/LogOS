#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import argparse
import pathlib
import re
import sys
import time


CHECKING_RE = re.compile(r"\bChecking\s+([^\s]+)\s+\(([^)]+)\)")


def main() -> int:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--out-tsv", required=True)
    parser.add_argument("--current-file", required=True)
    args = parser.parse_args()

    out_tsv = pathlib.Path(args.out_tsv)
    current_file = pathlib.Path(args.current_file)

    out_tsv.parent.mkdir(parents=True, exist_ok=True)
    out_fp = out_tsv.open("a", encoding="utf-8")

    start = time.monotonic()
    current_mod: str | None = None
    current_path: str | None = None
    current_start = start

    def emit_current(now: float) -> None:
        nonlocal current_mod, current_path, current_start
        if current_mod is None or current_path is None:
            return
        dur_ms = int(round((now - current_start) * 1000))
        out_fp.write(f"{current_mod}\t{dur_ms}\t{current_path}\n")
        out_fp.flush()

    for raw in sys.stdin:
        now = time.monotonic()
        elapsed = now - start
        sys.stdout.write(f"+{elapsed:7.1f}s {raw}")
        sys.stdout.flush()

        match = CHECKING_RE.search(raw)
        if not match:
            continue

        emit_current(now)

        current_mod = match.group(1)
        current_path = match.group(2)
        current_start = now

        try:
            current_file.write_text(current_mod, encoding="utf-8")
        except OSError:
            pass

    emit_current(time.monotonic())
    out_fp.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
