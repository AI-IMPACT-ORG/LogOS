#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import List

sys.dont_write_bytecode = True

from mm_emit_agda import emit_agda_database, emit_agda_database_chunks, emit_agda_hs_runner
from mm_error import MMError
from mm_parser import parse_mm


def main(argv: List[str]) -> int:
    ap = argparse.ArgumentParser(
        description="Parse a Metamath .mm database (supports $[ ... $] includes)."
    )
    ap.add_argument("mm_file", type=Path, help="Path to the root .mm file (e.g. set.mm).")
    ap.add_argument("--out", type=Path, default=None, help="Write parsed database JSON to this path.")
    ap.add_argument(
        "--emit-agda",
        type=Path,
        default=None,
        help="Emit an Agda module implementing `LogOS.Ports.Metamath.Database` for the parsed assertion prefix.",
    )
    ap.add_argument(
        "--agda-module",
        type=str,
        default="Metamath.SetMM",
        help="Agda module name to use with --emit-agda (must match output path).",
    )
    ap.add_argument(
        "--include-proofs",
        action="store_true",
        help="Include full $p proof token streams in the output JSON (can be huge).",
    )
    ap.add_argument(
        "--check-proofs",
        action="store_true",
        help="Check $p proofs while parsing (supports compressed proofs; can be slow on large DBs).",
    )
    ap.add_argument(
        "--progress-every",
        type=int,
        default=None,
        help="If set, print a progress line to stderr after every N parsed $a/$p assertions.",
    )
    ap.add_argument(
        "--max-assertions", type=int, default=None, help="Stop after parsing this many $a/$p assertions."
    )
    ap.add_argument(
        "--chunk-size",
        type=int,
        default=None,
        help="If set together with --emit-agda, emit a chunked Agda database (multiple modules) with this chunk size.",
    )
    ap.add_argument(
        "--emit-agda-runner",
        type=Path,
        default=None,
        help="Emit a small Agda runner (with Haskell backend FFI) that imports the emitted database and prints basic stats.",
    )
    ap.add_argument(
        "--runner-module",
        type=str,
        default=None,
        help="Agda module name to use with --emit-agda-runner (default: <agda-module>.Runner).",
    )
    args = ap.parse_args(argv)
    if args.max_assertions is not None and args.max_assertions <= 0:
        print(
            f"parse-mm: --max-assertions must be positive, got {args.max_assertions}",
            file=sys.stderr,
        )
        return 2
    if args.progress_every is not None and args.progress_every <= 0:
        print(
            f"parse-mm: --progress-every must be positive, got {args.progress_every}",
            file=sys.stderr,
        )
        return 2

    try:
        db = parse_mm(
            args.mm_file,
            include_proofs=args.include_proofs,
            max_assertions=args.max_assertions,
            check_proofs=args.check_proofs,
            progress_every=args.progress_every,
        )
    except MMError as e:
        print(f"parse-mm: ERROR: {e}", file=sys.stderr)
        return 2

    stats = db["stats"]
    assert isinstance(stats, dict)
    print(
        "Parsed:",
        f"{stats['num_constants']} constants,",
        f"{stats['num_variables']} variables,",
        f"{stats['num_floating']} $f,",
        f"{stats['num_essential']} $e,",
        f"{stats['num_a']} $a,",
        f"{stats['num_p']} $p",
    )

    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(db, indent=2, sort_keys=True), encoding="utf-8")
        print(f"Wrote: {args.out}")

    if args.emit_agda is not None:
        if args.chunk_size is None:
            emit_agda_database(db, args.emit_agda, module_name=args.agda_module)
            print(f"Wrote: {args.emit_agda}")
        else:
            emit_agda_database_chunks(
                db,
                args.emit_agda,
                module_name=args.agda_module,
                chunk_size=args.chunk_size,
            )
            print(
                f"Wrote: {args.emit_agda} (chunked; dir {args.emit_agda.parent / args.emit_agda.stem})"
            )

    if args.emit_agda_runner is not None:
        if args.emit_agda is None:
            print("parse-mm: ERROR: --emit-agda-runner requires --emit-agda", file=sys.stderr)
            return 2
        runner_mod = args.runner_module or f"{args.agda_module}.Runner"
        emit_agda_hs_runner(
            args.emit_agda_runner,
            module_name=runner_mod,
            db_module=args.agda_module,
        )
        print(f"Wrote: {args.emit_agda_runner}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
