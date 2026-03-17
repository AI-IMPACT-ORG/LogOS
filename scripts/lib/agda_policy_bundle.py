from __future__ import annotations

# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

sys.dont_write_bytecode = True


@dataclass(frozen=True)
class Check:
    name: str
    policy: str
    run: Callable[[Path], list[str]]


def strip_agda_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue

        if block_depth > 0:
            if ch == "-" and nxt == "}":
                block_depth -= 1
                out.append(" ")
                i += 2
                continue
            if ch == "{" and nxt == "-":
                block_depth += 1
                out.append(" ")
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue

        if ch == "{" and nxt == "-":
            block_depth = 1
            out.append(" ")
            i += 2
            continue

        if ch == "-" and nxt == "-":
            i = text.find("\n", i)
            if i == -1:
                break
            out.append("\n")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def iter_agda_files(base: Path) -> list[Path]:
    if not base.is_dir():
        return []
    return [p for p in sorted(base.rglob("*.agda")) if "_build" not in p.parts]


def check_bridge_contract(root: Path) -> list[str]:
    check_name = "bridge-contract-check"
    bridges_dir = root / "LogOS" / "Ports" / "Bridges"

    if not bridges_dir.is_dir():
        return []

    import_contract_re = re.compile(r"^\s*(?:open\s+import|import)\s+LogOS\.Ports\.Bridges\.Contract\b")
    bridge_contract_sig_re = re.compile(r"\bbridgeContract\b\s*:\s*BridgeContract\b")
    bridge_contract_def_re = re.compile(r"\bbridgeContract\b\s*=\s*")
    required_markers = (
        "BRIDGE-CONTRACT",
        "Source boundary:",
        "Target boundary:",
        "Intent:",
        "Why allowed:",
    )

    violations: list[str] = []
    for path in iter_agda_files(bridges_dir):
        if path.name == "Contract.agda":
            continue

        rel = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8")
        stripped = strip_agda_comments(text)

        for marker in required_markers:
            if marker not in text:
                violations.append(f"{rel}: missing bridge header marker: {marker!r}")

        if not any(import_contract_re.match(line) for line in stripped.splitlines()):
            violations.append(f"{rel}: missing import of LogOS.Ports.Bridges.Contract")

        if not bridge_contract_sig_re.search(stripped):
            violations.append(f"{rel}: missing typed bridgeContract : BridgeContract … …")

        if not bridge_contract_def_re.search(stripped):
            violations.append(f"{rel}: missing bridgeContract definition (= …)")

    return violations


def check_bridges_no_public_reexport(root: Path) -> list[str]:
    bridges_dir = root / "LogOS" / "Ports" / "Bridges"

    if not bridges_dir.is_dir():
        return []

    open_import_public_re = re.compile(r"^\s*open\s+import\b.*\bpublic\b", re.MULTILINE)

    violations: list[str] = []
    for path in iter_agda_files(bridges_dir):
        if path.name == "Contract.agda":
            continue

        rel = path.relative_to(root).as_posix()
        stripped = strip_agda_comments(path.read_text(encoding="utf-8"))

        m = open_import_public_re.search(stripped)
        if m:
            line_no = stripped[: m.start()].count("\n") + 1
            line = stripped.splitlines()[line_no - 1].strip()
            violations.append(f"{rel}:{line_no}: forbidden public re-export via open import: {line}")

    return violations


def check_no_proj12_displayed(root: Path) -> list[str]:
    check_name = "no-proj12-displayed-check"
    log_dir = root / "LogOS" / "LT" / "LOG"
    ports_dir = root / "LogOS" / "Ports"
    proj_tokens = ("proj₁", "proj₂")

    violations: list[str] = []

    if log_dir.is_dir():
        for path in iter_agda_files(log_dir):
            rel = path.relative_to(root).as_posix()
            stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
            if any(tok in stripped for tok in proj_tokens):
                violations.append(rel)

    if ports_dir.is_dir():
        for path in sorted(ports_dir.rglob("*2Cat.agda")):
            if "_build" in path.parts:
                continue
            rel = path.relative_to(root).as_posix()
            stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
            if any(tok in stripped for tok in proj_tokens):
                violations.append(rel)

    return violations


def check_ports_bridges_import(root: Path) -> list[str]:
    ports_dir = root / "LogOS" / "Ports"
    if not ports_dir.is_dir():
        return []

    import_re = re.compile(r"^\s*(?:open\s+import|import)\s+([A-Za-z0-9_.']+)\b")
    bridges_prefix = "LogOS.Ports.Bridges"

    allowed_importer_prefixes = (
        "LogOS/Ports/Bridges/",
        "LogOS/Ports/Quarantine/",
    )

    def allowed_importer(rel: str) -> bool:
        return any(rel.startswith(p) for p in allowed_importer_prefixes)

    violations: list[str] = []

    for path in iter_agda_files(ports_dir):
        rel = path.relative_to(root).as_posix()
        if allowed_importer(rel):
            continue

        text = strip_agda_comments(path.read_text(encoding="utf-8"))
        for i, line in enumerate(text.splitlines(), start=1):
            m = import_re.match(line)
            if not m:
                continue
            dep = m.group(1)
            if dep == bridges_prefix or dep.startswith(bridges_prefix + "."):
                violations.append(f"{rel}:{i}: forbidden import of bridge module from Ports: {dep}")

    return violations


def check_ports_funpreorder_usage(root: Path) -> list[str]:
    ports_dir = root / "LogOS" / "Ports"
    if not ports_dir.is_dir():
        return []

    import_funpreorder_re = re.compile(r"\b(?:open\s+import|import)\s+LogOS\.LT\.FunPreorder\b")
    funpreorder_token_re = re.compile(r"\b(?:FunPreorder|DFunPreorder)\b")

    allowed_prefixes = ("LogOS/Ports/Locality/",)
    allowed_files: set[str] = {"LogOS/Ports/Locality/Core.agda"}

    violations: list[str] = []
    for path in iter_agda_files(ports_dir):
        rel = path.relative_to(root).as_posix()
        if rel in allowed_files or any(rel.startswith(p) for p in allowed_prefixes):
            continue

        stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
        if import_funpreorder_re.search(stripped) or funpreorder_token_re.search(stripped):
            violations.append(rel)

    return violations


def check_globalise_import(root: Path) -> list[str]:
    logos_dir = root / "LogOS"
    if not logos_dir.is_dir():
        return []

    import_globalise_re = re.compile(r"\b(?:open\s+import|import)\s+LogOS\.Ports\.Globalise\b")

    allowed_files: set[str] = {
        "LogOS/Checks/ExtensionalityLadder.agda",
        "LogOS/Checks/Reachability/Ports.agda",
        "LogOS/Ports/BoundaryAsCode.agda",
        "LogOS/Ports/BoundaryAsCode/Uniform.agda",
    }

    violations: list[str] = []
    for path in iter_agda_files(logos_dir):
        rel = path.relative_to(root).as_posix()
        if rel in allowed_files:
            continue
        stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
        if import_globalise_re.search(stripped):
            violations.append(rel)

    return violations


def check_refinement_reasoning_usage(root: Path) -> list[str]:
    logos_dir = root / "LogOS"
    if not logos_dir.is_dir():
        return []

    allowed_trans_le_eq_files: set[str] = {
        "LogOS/LT/ConPreorder.agda",
    }
    allowed_conpreorder_trans_files: set[str] = {
        "LogOS/LT/ConPreorder.agda",
    }

    ident_cont_chars = r"\w'₀₁₂₃₄₅₆₇₈₉"
    trans_le_re = re.compile(rf"(?<![{ident_cont_chars}])trans⊑(?![{ident_cont_chars}])")
    trans_eq_re = re.compile(rf"(?<![{ident_cont_chars}])≈-trans(?![{ident_cont_chars}])")
    conpreorder_trans_re = re.compile(rf"\bConPreorder\.trans(?![{ident_cont_chars}])\b")

    violations: list[str] = []
    for path in iter_agda_files(logos_dir):
        rel = path.relative_to(root).as_posix()
        stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
        for i, line in enumerate(stripped.splitlines(), start=1):
            if rel not in allowed_trans_le_eq_files:
                if trans_le_re.search(line):
                    violations.append(
                        f"{rel}:{i}: forbidden direct use of `trans⊑` (use ConPreorder.Reasoning chains)"
                    )
                if trans_eq_re.search(line):
                    violations.append(
                        f"{rel}:{i}: forbidden direct use of `≈-trans` (use ConPreorder.Reasoning chains)"
                    )

            if rel not in allowed_conpreorder_trans_files:
                if conpreorder_trans_re.search(line):
                    violations.append(
                        f"{rel}:{i}: forbidden direct use of `ConPreorder.trans` (use ConPreorder.Reasoning chains)"
                    )

    return violations


def check_theorems_no_eq(root: Path) -> list[str]:
    theorems_dir = root / "LogOS" / "LT" / "Theorems"
    if not theorems_dir.is_dir():
        return []

    allowed_theorem_eq_files = {
        "LogOS/LT/Theorems/ArchitecturalNormalForm.agda",
    }

    violations: list[str] = []
    for path in iter_agda_files(theorems_dir):
        rel = path.relative_to(root).as_posix()
        if "Strictification" in path.parts or path.name.endswith("Strictification.agda"):
            continue
        if rel in allowed_theorem_eq_files:
            continue
        stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
        for i, line in enumerate(stripped.splitlines(), start=1):
            if "≡" in line:
                violations.append(f"{rel}:{i}")

    return violations


def check_conpreorder_open(root: Path) -> list[str]:
    logos_dir = root / "LogOS"
    if not logos_dir.is_dir():
        return []

    open_conpreorder_re = re.compile(r"\bopen\s+ConPreorder\b")

    violations: list[str] = []
    for path in iter_agda_files(logos_dir):
        rel = path.relative_to(root).as_posix()
        stripped = strip_agda_comments(path.read_text(encoding="utf-8"))
        for i, line in enumerate(stripped.splitlines(), start=1):
            if open_conpreorder_re.search(line):
                violations.append(f"{rel}:{i}")

    return violations


CHECKS: list[Check] = [
    Check(
        name="bridge-contract-check",
        policy=(
            "Every bridge module must declare its meaning-change contract explicitly "
            "(required BRIDGE-CONTRACT header markers + typed `bridgeContract`)."
        ),
        run=check_bridge_contract,
    ),
    Check(
        name="bridges-no-public-reexport-check",
        policy=(
            "Bridge modules must not re-export imports using `open import ... public` "
            "(keep meaning-change surfaces explicit; re-export belongs in API modules)."
        ),
        run=check_bridges_no_public_reexport,
    ),
    Check(
        name="no-proj12-displayed-check",
        policy=(
            "In displayed/Σ-totalised code, avoid `proj₁`/`proj₂`; use named projections "
            "`base`/`disp`/`baseHom`/`dispHom`."
        ),
        run=check_no_proj12_displayed,
    ),
    Check(
        name="ports-bridges-import-check",
        policy=(
            "Bridge modules (`LogOS.Ports.Bridges.*`) must not be imported from arbitrary "
            "`LogOS/Ports/**` modules; restrict to bridge entrypoints/wrappers."
        ),
        run=check_ports_bridges_import,
    ),
    Check(
        name="ports-funpreorder-usage-check",
        policy=(
            "`FunPreorder`/`DFunPreorder` are meaning-injection primitives; inside Ports, "
            "use them only at the canonical injection points `Locality`."
        ),
        run=check_ports_funpreorder_usage,
    ),
    Check(
        name="globalise-import-check",
        policy=(
            "`LogOS.Ports.Globalise` packages optional global coherence (“classical limit”); "
            "keep it quarantined to the canonical modules."
        ),
        run=check_globalise_import,
    ),
    Check(
        name="refinement-reasoning-usage-check",
        policy=(
            "Prefer refinement-chain reasoning combinators; forbid direct `trans⊑`/`≈-trans` "
            "and direct `ConPreorder.trans` outside the atomic spine."
        ),
        run=check_refinement_reasoning_usage,
    ),
    Check(
        name="theorems-no-eq-check",
        policy=(
            "Theorem modules are refinement-first and should not mention propositional equality (`≡`)."
        ),
        run=check_theorems_no_eq,
    ),
    Check(
        name="conpreorder-open-check",
        policy=(
            "Do not `open ConPreorder` downstream; use projections and reasoning combinators."
        ),
        run=check_conpreorder_open,
    ),
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run bundled LogOS Agda policy checks.")
    parser.add_argument(
        "--only",
        action="append",
        default=[],
        metavar="CHECK_NAME",
        help="Run only a specific sub-check (repeatable).",
    )
    return parser.parse_args()


def main() -> int:
    root = Path(".").resolve()
    args = parse_args()

    checks = CHECKS
    if args.only:
        wanted = set(args.only)
        checks = [c for c in CHECKS if c.name in wanted]
        unknown = sorted(wanted.difference({c.name for c in CHECKS}))
        if unknown:
            print("agda-policy-bundle: FAIL", file=sys.stderr)
            print("Unknown --only check names:", file=sys.stderr)
            for name in unknown:
                print(f"  - {name}", file=sys.stderr)
            print("Known checks:", file=sys.stderr)
            for c in CHECKS:
                print(f"  - {c.name}", file=sys.stderr)
            return 2

    all_violations: dict[str, list[str]] = {}
    for check in checks:
        violations = check.run(root)
        if violations:
            all_violations[check.name] = violations

    if all_violations:
        print("agda-policy-bundle-check: FAIL", file=sys.stderr)
        for check in checks:
            violations = all_violations.get(check.name)
            if not violations:
                continue
            print(f"\n== {check.name} ==", file=sys.stderr)
            print(f"Policy: {check.policy}", file=sys.stderr)
            print("Violations:", file=sys.stderr)
            for v in violations:
                print(f"  - {v}", file=sys.stderr)
        return 1

    print("agda-policy-bundle-check: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
