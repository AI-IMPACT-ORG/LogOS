#!/usr/bin/env bash
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only
# Policy:
# - The cold CI umbrella should cover the full host-mechanized Agda surface
#   (`LogOS/**/*.agda` plus `docs/**/*.lagda.md`).
# - The repository tracks an "assumption-light" Agda sub-surface: modules whose
#   import closure stays outside ledger-declared assumption usage.
# - This second metric is a syntactic CI trend metric, not a semantic theorem:
#   assumption providers come from the canonical assumptions ledger and direct
#   usage is detected symbol-wise after stripping Agda comments.

set -euo pipefail

CHECK_NAME="proof-coverage-check"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/check_common.sh
source "${SCRIPT_DIR}/lib/check_common.sh"

die() { check_die "${CHECK_NAME}" "$*"; }

ROOT="$(check_repo_root "${BASH_SOURCE[0]}")"
cd "${ROOT}"

check_require_cmd "${CHECK_NAME}" python3

python3 - <<'PY'
from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(".").resolve()
LOGOS_DIR = ROOT / "LogOS"
DOCS_DIR = ROOT / "docs"
LEDGER = ROOT / "docs" / "Core" / "Meta" / "Assumptions_Ledger.md"
THRESHOLDS = ROOT / "scripts" / "proof_coverage_thresholds.tsv"
OUT = ROOT / "_build" / "metrics" / "proof_coverage.json"

IMPORT_RE = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b", re.M)
MODULE_RE = re.compile(r"^module\s+([A-Za-z0-9_.']+)\s+where", re.M)
INTRO_RE = re.compile(r"^- Introduced: `([^`]+)`(.*)$")
TOKEN_BOUNDARY = r"A-Za-z0-9_.'"


@dataclass(frozen=True)
class Thresholds:
    assumption_light_module_pct: float
    assumption_light_loc_pct: float


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def count_loc(paths: set[Path]) -> int:
    total = 0
    for path in paths:
        with path.open(encoding="utf-8") as handle:
            total += sum(1 for _ in handle)
    return total


def pct(numer: int, denom: int) -> float:
    return 100.0 if denom == 0 else 100.0 * numer / denom


def strip_agda_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)

    while i < n:
        if depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue

        if text.startswith("{-", i):
            depth += 1
            i += 2
            continue

        if depth > 0:
            if text.startswith("{-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-}", i):
                depth -= 1
                i += 2
                continue
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def load_thresholds(path: Path) -> Thresholds:
    if not path.is_file():
        raise RuntimeError(f"missing thresholds file: {rel(path)}")

    raw: dict[str, float] = {}
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        cols = stripped.split("\t")
        if len(cols) != 2:
            raise RuntimeError(f"{rel(path)}:{i}: expected <metric><TAB><float>")
        key, value = cols
        try:
            raw[key] = float(value)
        except ValueError as exc:
            raise RuntimeError(f"{rel(path)}:{i}: invalid float {value!r}") from exc

    expected = {"assumption_light_module_pct", "assumption_light_loc_pct"}
    missing = expected - raw.keys()
    extra = raw.keys() - expected
    if missing:
        raise RuntimeError(f"{rel(path)}: missing thresholds: {', '.join(sorted(missing))}")
    if extra:
        raise RuntimeError(f"{rel(path)}: unknown thresholds: {', '.join(sorted(extra))}")

    return Thresholds(
        assumption_light_module_pct=raw["assumption_light_module_pct"],
        assumption_light_loc_pct=raw["assumption_light_loc_pct"],
    )


def load_assumption_entries(path: Path) -> list[tuple[str, tuple[str, ...]]]:
    if not path.is_file():
        raise RuntimeError(f"missing assumptions ledger: {rel(path)}")

    entries: list[tuple[str, tuple[str, ...]]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        m = INTRO_RE.match(line.strip())
        if not m:
            continue
        module_path, rest = m.groups()
        if not module_path.endswith(".agda"):
            continue
        symbols = tuple(sym for sym in re.findall(r"`([^`]+)`", rest) if sym)
        entries.append((module_path, symbols))

    if not entries:
        raise RuntimeError(f"{rel(path)}: no assumption entries found")

    return entries


def module_from_path(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    m = MODULE_RE.search(text)
    if not m:
        raise RuntimeError(f"missing module declaration: {rel(path)}")
    return m.group(1)


def build_module_graph() -> tuple[dict[str, Path], dict[Path, str], dict[str, set[str]], dict[str, str]]:
    module_to_path: dict[str, Path] = {}
    path_to_module: dict[Path, str] = {}
    imports: dict[str, set[str]] = {}
    stripped_texts: dict[str, str] = {}

    for path in sorted(LOGOS_DIR.rglob("*.agda")):
        if "_build" in path.parts:
            continue
        module_name = module_from_path(path)
        if module_name in module_to_path:
            raise RuntimeError(
                f"duplicate module name {module_name}: {rel(module_to_path[module_name])} and {rel(path)}"
            )
        module_to_path[module_name] = path
        path_to_module[path] = module_name
        stripped_texts[module_name] = strip_agda_comments(path.read_text(encoding="utf-8"))

    for module_name, path in module_to_path.items():
        deps = set(IMPORT_RE.findall(stripped_texts[module_name]))
        imports[module_name] = {dep for dep in deps if dep in module_to_path}

    return module_to_path, path_to_module, imports, stripped_texts


def reverse_closure(imports: dict[str, set[str]], starts: set[str]) -> set[str]:
    rev: dict[str, set[str]] = {module_name: set() for module_name in imports}
    for module_name, deps in imports.items():
        for dep in deps:
            rev[dep].add(module_name)

    seen: set[str] = set()
    stack = list(starts)
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rev[cur] - seen)
    return seen


def gather_host_surface() -> dict[str, object]:
    agda_all = {path for path in LOGOS_DIR.rglob("*.agda") if "_build" not in path.parts}
    core = {
        path
        for path in agda_all
        if "Apps" not in path.relative_to(LOGOS_DIR).parts and "Adapters" not in path.relative_to(LOGOS_DIR).parts
    }
    integration = agda_all - core
    docs = {path for path in DOCS_DIR.rglob("*.lagda.md") if "_build" not in path.parts}

    overlap = core & integration
    missing = agda_all - (core | integration)
    extra = (core | integration) - agda_all
    if overlap or missing or extra:
        chunks: list[str] = []
        if overlap:
            chunks.append(f"overlap between core/integration: {', '.join(sorted(rel(p) for p in overlap))}")
        if missing:
            chunks.append(f"missing Agda files from host coverage: {', '.join(sorted(rel(p) for p in missing))}")
        if extra:
            chunks.append(f"unexpected Agda files in host coverage: {', '.join(sorted(rel(p) for p in extra))}")
        raise RuntimeError("; ".join(chunks))

    return {
        "agda_total_modules": len(agda_all),
        "agda_total_loc": count_loc(agda_all),
        "agda_covered_modules": len(core | integration),
        "agda_covered_loc": count_loc(core | integration),
        "docs_total_modules": len(docs),
        "docs_total_loc": count_loc(docs),
        "docs_covered_modules": len(docs),
        "docs_covered_loc": count_loc(docs),
    }


def gather_assumption_surface(
    *,
    module_to_path: dict[str, Path],
    path_to_module: dict[Path, str],
    imports: dict[str, set[str]],
    stripped_texts: dict[str, str],
) -> dict[str, object]:
    entries = load_assumption_entries(LEDGER)

    provider_modules: set[str] = set()
    symbol_to_paths: dict[str, set[str]] = {}
    for module_path, symbols in entries:
        provider_path = ROOT / module_path
        if provider_path in path_to_module:
            provider_modules.add(path_to_module[provider_path])
        for symbol in symbols:
            symbol_to_paths.setdefault(symbol, set()).add(module_path)

    patterns = {
        symbol: re.compile(
            rf"(?<![{TOKEN_BOUNDARY}]){re.escape(symbol)}(?![{TOKEN_BOUNDARY}])"
        )
        for symbol in symbol_to_paths
    }

    direct_users = set(provider_modules)
    direct_user_symbols: dict[str, set[str]] = {module_name: set() for module_name in module_to_path}
    for module_name, text in stripped_texts.items():
        for symbol, pattern in patterns.items():
            if pattern.search(text):
                direct_users.add(module_name)
                direct_user_symbols[module_name].add(symbol)

    sensitive = reverse_closure(imports, direct_users)
    light = set(module_to_path) - sensitive

    return {
        "assumption_entries": len(entries),
        "assumption_symbols": len(symbol_to_paths),
        "provider_modules": len(provider_modules),
        "direct_user_modules": len(direct_users),
        "direct_user_loc": count_loc({module_to_path[m] for m in direct_users}),
        "sensitive_modules": len(sensitive),
        "sensitive_loc": count_loc({module_to_path[m] for m in sensitive}),
        "light_modules": len(light),
        "light_loc": count_loc({module_to_path[m] for m in light}),
        "total_modules": len(module_to_path),
        "total_loc": count_loc(set(module_to_path.values())),
    }


def main() -> int:
    try:
        thresholds = load_thresholds(THRESHOLDS)
        host = gather_host_surface()
        module_to_path, path_to_module, imports, stripped_texts = build_module_graph()
        assumptions = gather_assumption_surface(
            module_to_path=module_to_path,
            path_to_module=path_to_module,
            imports=imports,
            stripped_texts=stripped_texts,
        )
    except RuntimeError as exc:
        print("proof-coverage-check: FAIL", file=sys.stderr)
        print(f"  - {exc}", file=sys.stderr)
        return 1

    host_agda_module_pct = pct(host["agda_covered_modules"], host["agda_total_modules"])
    host_agda_loc_pct = pct(host["agda_covered_loc"], host["agda_total_loc"])
    host_docs_module_pct = pct(host["docs_covered_modules"], host["docs_total_modules"])
    host_docs_loc_pct = pct(host["docs_covered_loc"], host["docs_total_loc"])

    assumption_light_module_pct = pct(assumptions["light_modules"], assumptions["total_modules"])
    assumption_light_loc_pct = pct(assumptions["light_loc"], assumptions["total_loc"])

    violations: list[str] = []
    if host_agda_module_pct < 100.0 or host_agda_loc_pct < 100.0:
        violations.append(
            "host Agda coverage dropped below 100%"
            f" ({host['agda_covered_modules']}/{host['agda_total_modules']} modules,"
            f" {host['agda_covered_loc']}/{host['agda_total_loc']} LOC)"
        )
    if host_docs_module_pct < 100.0 or host_docs_loc_pct < 100.0:
        violations.append(
            "host literate coverage dropped below 100%"
            f" ({host['docs_covered_modules']}/{host['docs_total_modules']} modules,"
            f" {host['docs_covered_loc']}/{host['docs_total_loc']} LOC)"
        )
    if assumption_light_module_pct + 1e-9 < thresholds.assumption_light_module_pct:
        violations.append(
            "assumption-light module coverage below floor"
            f" ({assumption_light_module_pct:.2f}% < {thresholds.assumption_light_module_pct:.2f}%)"
        )
    if assumption_light_loc_pct + 1e-9 < thresholds.assumption_light_loc_pct:
        violations.append(
            "assumption-light LOC coverage below floor"
            f" ({assumption_light_loc_pct:.2f}% < {thresholds.assumption_light_loc_pct:.2f}%)"
        )

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(
        json.dumps(
            {
                "host_mechanization": {
                    "agda": {
                        "modules": {
                            "covered": host["agda_covered_modules"],
                            "total": host["agda_total_modules"],
                            "percent": round(host_agda_module_pct, 4),
                        },
                        "loc": {
                            "covered": host["agda_covered_loc"],
                            "total": host["agda_total_loc"],
                            "percent": round(host_agda_loc_pct, 4),
                        },
                    },
                    "docs": {
                        "modules": {
                            "covered": host["docs_covered_modules"],
                            "total": host["docs_total_modules"],
                            "percent": round(host_docs_module_pct, 4),
                        },
                        "loc": {
                            "covered": host["docs_covered_loc"],
                            "total": host["docs_total_loc"],
                            "percent": round(host_docs_loc_pct, 4),
                        },
                    },
                },
                "assumption_light": {
                    "entries": assumptions["assumption_entries"],
                    "symbols": assumptions["assumption_symbols"],
                    "direct_users": {
                        "modules": assumptions["direct_user_modules"],
                        "loc": assumptions["direct_user_loc"],
                    },
                    "sensitive_closure": {
                        "modules": assumptions["sensitive_modules"],
                        "loc": assumptions["sensitive_loc"],
                    },
                    "light": {
                        "modules": assumptions["light_modules"],
                        "total_modules": assumptions["total_modules"],
                        "module_percent": round(assumption_light_module_pct, 4),
                        "loc": assumptions["light_loc"],
                        "total_loc": assumptions["total_loc"],
                        "loc_percent": round(assumption_light_loc_pct, 4),
                    },
                    "thresholds": {
                        "module_percent_floor": thresholds.assumption_light_module_pct,
                        "loc_percent_floor": thresholds.assumption_light_loc_pct,
                    },
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    if violations:
        print("proof-coverage-check: FAIL", file=sys.stderr)
        for violation in violations:
            print(f"  - {violation}", file=sys.stderr)
        print(f"  - report written to {rel(OUT)}", file=sys.stderr)
        return 1

    print("proof-coverage-check: OK")
    print(
        "  host Agda coverage:"
        f" {host['agda_covered_modules']}/{host['agda_total_modules']} modules,"
        f" {host['agda_covered_loc']}/{host['agda_total_loc']} LOC"
        f" ({host_agda_module_pct:.2f}% / {host_agda_loc_pct:.2f}%)"
    )
    print(
        "  host literate coverage:"
        f" {host['docs_covered_modules']}/{host['docs_total_modules']} modules,"
        f" {host['docs_covered_loc']}/{host['docs_total_loc']} LOC"
        f" ({host_docs_module_pct:.2f}% / {host_docs_loc_pct:.2f}%)"
    )
    print(
        "  assumption-light Agda coverage:"
        f" {assumptions['light_modules']}/{assumptions['total_modules']} modules,"
        f" {assumptions['light_loc']}/{assumptions['total_loc']} LOC"
        f" ({assumption_light_module_pct:.2f}% / {assumption_light_loc_pct:.2f}%)"
    )
    print(
        "  assumption-sensitive closure:"
        f" {assumptions['sensitive_modules']}/{assumptions['total_modules']} modules,"
        f" {assumptions['sensitive_loc']}/{assumptions['total_loc']} LOC"
    )
    print(
        "  ledger roots:"
        f" {assumptions['assumption_entries']} entries,"
        f" {assumptions['assumption_symbols']} symbols,"
        f" {assumptions['direct_user_modules']} direct user/provider modules"
    )
    print(
        "  floors:"
        f" {thresholds.assumption_light_module_pct:.2f}% modules,"
        f" {thresholds.assumption_light_loc_pct:.2f}% LOC"
    )
    print(f"  report: {rel(OUT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
PY
