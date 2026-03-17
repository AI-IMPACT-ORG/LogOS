#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - Allowlists are quarantines: every entry must be justified, unique, and non-stale.
# - Do not hide checks from the CI baseline via policy_coverage_allowlist (must stay empty).
# - Do not quarantine layer-order violations (layer_order_allowlist must stay empty).
# - Postulate allowlist is permitted but must be minimal and justified.

set -euo pipefail

CHECK_NAME="stale-allowlists-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"
# shellcheck source=scripts/lib/layers.sh
source "${SCRIPT_DIR}/lib/layers.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

LAYERS_CSV="$(layers_csv)"

LAYERS_CSV="${LAYERS_CSV}" python3 - <<'PY'
from __future__ import annotations

import os
import re
import sys
from pathlib import Path
from collections import defaultdict

CHECK_NAME = "stale-allowlists-check"
ROOT = Path(".").resolve()
SCRIPTS_DIR = ROOT / "scripts"

LAYER_ORDER_ALLOWLIST = SCRIPTS_DIR / "layer_order_allowlist.txt"
POLICY_COVERAGE_ALLOWLIST = SCRIPTS_DIR / "policy_coverage_allowlist.txt"
POSTULATE_ALLOWLIST = SCRIPTS_DIR / "postulate_allowlist.txt"

DOCS_POLICY = ROOT / "docs" / "Core" / "Policy" / "Agda_Allowlist_Policy.md"


def parse_allowlist_with_justifications(path: Path, *, allow_inline_comment: bool) -> tuple[list[str], list[str]]:
    """
    Returns (entries, errors).

    Justification rule: every entry must have either
    - an inline comment after '#', OR
    - an immediately preceding non-blank comment line.
    """
    errors: list[str] = []
    entries: list[str] = []

    last_nonblank_kind: str | None = None  # "comment" | "entry"
    last_comment_text: str = ""
    last_comment_lineno: int = 0

    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.rstrip("\n")
        stripped = line.strip()
        if not stripped:
            continue

        if stripped.startswith("#"):
            last_nonblank_kind = "comment"
            last_comment_lineno = lineno
            last_comment_text = stripped.lstrip("#").strip()
            continue

        inline_just = ""
        entry_text = stripped
        if allow_inline_comment and "#" in stripped:
            entry_text, inline_just = stripped.split("#", 1)
            entry_text = entry_text.strip()
            inline_just = inline_just.strip()

        if not entry_text:
            continue

        has_prev_just = last_nonblank_kind == "comment" and last_comment_text and last_comment_lineno > 0
        has_inline_just = bool(inline_just)
        if not (has_prev_just or has_inline_just):
            rel = path.relative_to(ROOT).as_posix()
            errors.append(f"{rel}:{lineno}: allowlist entry lacks justification comment: {entry_text!r}")

        entries.append(entry_text)
        last_nonblank_kind = "entry"

    # Require uniqueness (avoid “same bypass twice”).
    dups: list[str] = sorted({e for e in entries if entries.count(e) > 1})
    if dups:
        rel = path.relative_to(ROOT).as_posix()
        for d in dups:
            errors.append(f"{rel}: duplicate allowlist entry: {d!r}")

    return entries, errors


def collect_entries_by_list() -> tuple[dict[str, list[str]], list[str]]:
    entries_by_file: dict[Path, list[str]] = {}
    errors: list[str] = []

    def read(name: str, path: Path, allow_inline_comment: bool) -> None:
        if not path.is_file():
            errors.append(f"missing allowlist file: {path.relative_to(ROOT).as_posix()}")
            entries_by_file[path] = []
            return

        entries, errs = parse_allowlist_with_justifications(path, allow_inline_comment=allow_inline_comment)
        entries_by_file[path] = entries
        errors.extend(f"{path.relative_to(ROOT).as_posix()}: {e}" for e in errs)

    read("layer_order_allowlist", LAYER_ORDER_ALLOWLIST, allow_inline_comment=False)
    read("policy_coverage_allowlist", POLICY_COVERAGE_ALLOWLIST, allow_inline_comment=True)
    read("postulate_allowlist", POSTULATE_ALLOWLIST, allow_inline_comment=True)
    return entries_by_file, errors


def layer_order_violations() -> list[str]:
    import pathlib

    logos_dir = ROOT / "LogOS"
    if not logos_dir.is_dir():
        return []

    layers = [layer for layer in os.environ.get("LAYERS_CSV", "").split(",") if layer]
    layer_index: dict[str, int] = {layer: i for i, layer in enumerate(layers)}

    import_re = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)")

    def category(mod: str) -> str:
        parts = mod.split(".")
        if len(parts) < 2 or parts[0] != "LogOS":
            return parts[0]
        return parts[1]

    agda_files = [p for p in logos_dir.rglob("*.agda") if "_build" not in p.parts]
    modules: dict[str, pathlib.Path] = {}
    for path in agda_files:
        mod = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        modules[mod] = path

    out: set[str] = set()

    for mod, path in modules.items():
        src_cat = category(mod)
        src_path = path.relative_to(ROOT).as_posix()
        if src_cat not in layer_index:
            out.add(f"{src_path}: unknown LogOS category '{src_cat}' (update scripts/lib/layers.sh)")
            continue
        src_layer = layer_index[src_cat]

        for line in path.read_text(encoding="utf-8").splitlines():
            match = import_re.match(line)
            if not match:
                continue
            dep = match.group(1)
            if dep not in modules:
                continue
            dep_cat = category(dep)
            if dep_cat not in layer_index:
                continue
            dep_layer = layer_index[dep_cat]
            if src_layer < dep_layer:
                out.add(f"{src_path}: {src_cat}({src_layer}) imports {dep} [{dep_cat}({dep_layer})]")

    return sorted(out)


def postulate_pattern_present(path: Path) -> bool:
    # Keep in sync with scripts/postulate_policy_check.sh.
    postulate_re = re.compile(r"^[ \t]*postulate(?:[ \t]|$)", flags=re.MULTILINE)
    return bool(postulate_re.search(path.read_text(encoding="utf-8")))


def policy_coverage_missing_for(script_basename: str) -> bool:
    # Mirror scripts/policy_coverage_check.sh: allowlisting is only meaningful if
    # the script would otherwise be required.
    makefile = ROOT / "Makefile"
    if not makefile.is_file():
        return True

    all_scripts = {p.name for p in (ROOT / "scripts" / "check").glob("*_check.sh")}
    if script_basename not in all_scripts:
        return True

    mk = makefile.read_text(encoding="utf-8")
    m = re.search(r"^ci-policy:(.*)$", mk, flags=re.MULTILINE)
    if not m:
        return True
    ci_deps = [w for w in m.group(1).strip().split() if w]

    target = script_basename.removesuffix(".sh").replace("_", "-")
    if not re.search(rf"^{re.escape(target)}:", mk, flags=re.MULTILINE):
        return True
    if f"scripts/check/{script_basename}" not in mk:
        return True
    if target not in ci_deps:
        return True
    # Fully wired → allowlist entry is stale.
    return False


def main() -> int:
    errors: list[str] = []

    entries_by_file, parse_errors = collect_entries_by_list()
    errors.extend(parse_errors)

    # --- allowlist by file -----------------------------------------------
    layer_order_entries = entries_by_file[LAYER_ORDER_ALLOWLIST]
    policy_coverage_entries = entries_by_file[POLICY_COVERAGE_ALLOWLIST]
    postulate_entries = entries_by_file[POSTULATE_ALLOWLIST]

    if layer_order_entries:
        rel = LAYER_ORDER_ALLOWLIST.relative_to(ROOT).as_posix()
        errors.append(f"{rel}: layer-order allowlist must stay empty (fix layering violations instead of quarantining them)")

    # Check stale / invalid entries by list category.
    viols = layer_order_violations()

    if policy_coverage_entries:
        rel = POLICY_COVERAGE_ALLOWLIST.relative_to(ROOT).as_posix()
        errors.append(f"{rel}: policy coverage allowlist is not allowed to hide baseline checks")

    for e in layer_order_entries:
        if not any(e in v for v in viols):
            rel = LAYER_ORDER_ALLOWLIST.relative_to(ROOT).as_posix()
            errors.append(f"{rel}: stale allowlist entry (matches no current violation): {e!r}")

    for e in policy_coverage_entries:
        # Entry format is a script basename (e.g. foo_check.sh).
        if not policy_coverage_missing_for(e):
            rel = POLICY_COVERAGE_ALLOWLIST.relative_to(ROOT).as_posix()
            errors.append(f"{rel}: stale allowlist entry (script is now fully wired into ci-policy): {e!r}")

    for e in postulate_entries:
        p = (ROOT / e).resolve()
        try:
            rel = p.relative_to(ROOT).as_posix()
        except ValueError:
            rel = e
        if not p.is_file():
            errors.append(f"{POSTULATE_ALLOWLIST.relative_to(ROOT).as_posix()}: missing allowlisted file: {e!r}")
            continue
        if not postulate_pattern_present(p):
            errors.append(
                f"{POSTULATE_ALLOWLIST.relative_to(ROOT).as_posix()}: stale allowlist entry (file has no postulate): {e!r}"
            )

    # No entry may be active in multiple allowlists.
    overlap: dict[str, list[str]] = defaultdict(list)
    for path, entries in entries_by_file.items():
        rel = path.relative_to(ROOT).as_posix()
        for entry in entries:
            overlap[entry].append(rel)

    for entry, files in sorted(overlap.items()):
        uniq_files = sorted(set(files))
        if len(uniq_files) > 1:
            errors.append(
                f"allowlist overlap: entry {entry!r} appears in multiple allowlists: "
                + ", ".join(uniq_files)
            )

    if not DOCS_POLICY.exists():
        errors.append(
            f"docs policy missing: expected {DOCS_POLICY.relative_to(ROOT).as_posix()} "
            "to describe allowlist category boundaries and overlap restrictions"
        )

    if errors:
        print(f"{CHECK_NAME}: FAIL", file=sys.stderr)
        print("Allowlist hygiene violations:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print(f"{CHECK_NAME}: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
