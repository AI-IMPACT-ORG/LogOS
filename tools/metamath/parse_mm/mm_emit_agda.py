#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Set

from mm_error import MMError


def _require_field(mapping: Dict[str, object], key: str, owner: str) -> object:
    try:
        return mapping[key]
    except KeyError as e:
        raise MMError(f"{owner} is missing required field {key!r}") from e


def _expect_dict(value: object, name: str) -> Dict[str, object]:
    if not isinstance(value, dict):
        raise MMError(f"{name} must be a dict, got {type(value).__name__}")
    return value


def _expect_list(value: object, name: str) -> List[object]:
    if not isinstance(value, list):
        raise MMError(f"{name} must be a list, got {type(value).__name__}")
    return value


def _expect_str(value: object, name: str) -> str:
    if not isinstance(value, str):
        raise MMError(f"{name} must be a string, got {type(value).__name__}")
    return value


def _expect_str_list(value: object, name: str) -> List[str]:
    items = _expect_list(value, name)
    out: List[str] = []
    for i, item in enumerate(items):
        out.append(_expect_str(item, f"{name}[{i}]"))
    return out


def _validate_db_tables(
    db: Dict[str, object],
) -> tuple[List[Dict[str, object]], Dict[str, object], Dict[str, object]]:
    assertions_raw = _expect_list(_require_field(db, "assertions", "db"), "db['assertions']")
    floating = _expect_dict(_require_field(db, "floating", "db"), "db['floating']")
    essential = _expect_dict(_require_field(db, "essential", "db"), "db['essential']")

    assertions: List[Dict[str, object]] = []
    for i, item in enumerate(assertions_raw):
        assertions.append(_expect_dict(item, f"db['assertions'][{i}]"))

    return assertions, floating, essential


def _floating_formula(floating: Dict[str, object], label: str, owner: str) -> List[str]:
    fh = _expect_dict(_require_field(floating, label, owner), f"{owner}[{label!r}]")
    typecode = _expect_str(
        _require_field(fh, "typecode", f"{owner}[{label!r}]"),
        f"{owner}[{label!r}]['typecode']",
    )
    var = _expect_str(
        _require_field(fh, "var", f"{owner}[{label!r}]"),
        f"{owner}[{label!r}]['var']",
    )
    return [typecode, var]


def _essential_expr(essential: Dict[str, object], label: str, owner: str) -> List[str]:
    return _expect_str_list(
        _require_field(essential, label, owner),
        f"{owner}[{label!r}]",
    )


def _agda_list_nat(xs: List[int]) -> str:
    if not xs:
        return "[]"
    return "(" + " ∷ ".join(str(x) for x in xs) + " ∷ []" + ")"


def _agda_list_formula(formulas: List[List[int]]) -> str:
    if not formulas:
        return "[]"
    parts = [_agda_list_nat(f) for f in formulas]
    return "(" + " ∷ ".join(parts) + " ∷ []" + ")"


def _agda_list_list_formula(rows: List[List[List[int]]]) -> str:
    if not rows:
        return "[]"
    parts = [_agda_list_formula(r) for r in rows]
    return "(" + " ∷ ".join(parts) + " ∷ []" + ")"


def emit_agda_database(
    db: Dict[str, object],
    out_path: Path,
    *,
    module_name: str,
) -> None:
    assertions, floating, essential = _validate_db_tables(db)

    # Collect all tokens appearing in any hypothesis/conclusion of the chosen assertions.
    sym_set: Set[str] = set()

    def add_expr(expr: List[str]) -> None:
        for t in expr:
            sym_set.add(t)

    for i, a in enumerate(assertions):
        owner = f"db['assertions'][{i}]"
        add_expr(_expect_str_list(_require_field(a, "expr", owner), f"{owner}['expr']"))

        for flbl in _expect_str_list(_require_field(a, "float_hyps", owner), f"{owner}['float_hyps']"):
            add_expr(_floating_formula(floating, flbl, "db['floating']"))

        for elbl in _expect_str_list(_require_field(a, "ess_hyps", owner), f"{owner}['ess_hyps']"):
            add_expr(_essential_expr(essential, elbl, "db['essential']"))

    syms = sorted(sym_set)
    sym_index = {s: i for (i, s) in enumerate(syms)}

    def enc(expr: List[str]) -> List[int]:
        return [sym_index[t] for t in expr]

    # Encode each assertion as a (premises, conclusion) row.
    premises_rows: List[List[List[int]]] = []
    concl_rows: List[List[int]] = []
    label_rows: List[str] = []

    for i, a in enumerate(assertions):
        owner = f"db['assertions'][{i}]"
        label_rows.append(str(_require_field(a, "label", owner)))
        concl_rows.append(enc(_expect_str_list(_require_field(a, "expr", owner), f"{owner}['expr']")))

        premises: List[List[int]] = []
        for flbl in _expect_str_list(_require_field(a, "float_hyps", owner), f"{owner}['float_hyps']"):
            premises.append(enc(_floating_formula(floating, flbl, "db['floating']")))
        for elbl in _expect_str_list(_require_field(a, "ess_hyps", owner), f"{owner}['ess_hyps']"):
            premises.append(enc(_essential_expr(essential, elbl, "db['essential']")))
        premises_rows.append(premises)

    out_path.parent.mkdir(parents=True, exist_ok=True)

    lines: List[str] = []
    lines.append("{-")
    lines.append("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI")
    lines.append("Copyright (C) 2026 AI.IMPACT GmbH")
    lines.append("SPDX-License-Identifier: GPL-3.0-only")
    lines.append("-}")
    lines.append("")
    lines.append("{-# OPTIONS --safe #-}")
    lines.append(f"module {module_name} where")
    lines.append("")
    lines.append("open import LogOS.Prelude")
    lines.append("open import LogOS.Prelude.List using (List; []; _∷_)")
    lines.append("")
    lines.append("import LogOS.Ports.Metamath as MM")
    lines.append("")
    lines.append("-- Formulas are token lists (symbols are interned as Nat indices).")
    lines.append("Formula : Set")
    lines.append("Formula = List ℕ")
    lines.append("")
    lines.append("numSymbols : ℕ")
    lines.append(f"numSymbols = {len(syms)}")
    lines.append("")
    lines.append("numAssertions : ℕ")
    lines.append(f"numAssertions = {len(assertions)}")
    lines.append("")
    lines.append("-- Symbol table (index -> original token).")
    for i, s in enumerate(syms):
        lines.append(f"-- {i}: {s}")
    lines.append("")
    lines.append("-- Assertion index -> original Metamath label.")
    for i, lab in enumerate(label_rows):
        lines.append(f"-- {i}: {lab}")
    lines.append("")
    lines.append("premisesTable : List (List Formula)")
    lines.append(f"premisesTable = {_agda_list_list_formula(premises_rows)}")
    lines.append("")
    lines.append("conclTable : List Formula")
    lines.append(f"conclTable = {_agda_list_formula(concl_rows)}")
    lines.append("")
    lines.append("lookup : ∀ {A : Set} → ℕ → List A → A → A")
    lines.append("lookup zero (x ∷ xs) d = x")
    lines.append("lookup (suc n) (x ∷ xs) d = lookup n xs d")
    lines.append("lookup _ [] d = d")
    lines.append("")
    lines.append("hyps : ℕ → List Formula")
    lines.append("hyps n = lookup n premisesTable []")
    lines.append("")
    lines.append("concl : ℕ → Formula")
    lines.append("concl n = lookup n conclTable []")
    lines.append("")
    lines.append("DB : MM.Database Formula")
    lines.append("DB = record { Label = ℕ ; hyps = hyps ; concl = concl }")
    lines.append("")
    lines.append("-- Derived: closure transformer for this database.")
    lines.append("module Closed = MM.FromDB DB")
    lines.append("")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _agda_nat_pat(k: int) -> str:
    # Pattern for a concrete Nat using suc/zero, to avoid relying on numeric literals in patterns.
    if k < 0:
        raise MMError(f"Nat pattern index must be non-negative, got {k}")
    return "suc (" * k + "zero" + ")" * k


def emit_agda_database_chunks(
    db: Dict[str, object],
    out_path: Path,
    *,
    module_name: str,
    chunk_size: int,
) -> None:
    if chunk_size <= 0:
        raise MMError(f"chunk_size must be positive, got {chunk_size}")

    assertions, floating, essential = _validate_db_tables(db)

    # Global symbol table for all emitted chunks.
    sym_set: Set[str] = set()

    def add_expr(expr: List[str]) -> None:
        for t in expr:
            sym_set.add(t)

    for i, a in enumerate(assertions):
        owner = f"db['assertions'][{i}]"
        add_expr(_expect_str_list(_require_field(a, "expr", owner), f"{owner}['expr']"))

        for flbl in _expect_str_list(_require_field(a, "float_hyps", owner), f"{owner}['float_hyps']"):
            add_expr(_floating_formula(floating, flbl, "db['floating']"))

        for elbl in _expect_str_list(_require_field(a, "ess_hyps", owner), f"{owner}['ess_hyps']"):
            add_expr(_essential_expr(essential, elbl, "db['essential']"))

    syms = sorted(sym_set)
    sym_index = {s: i for (i, s) in enumerate(syms)}

    def enc(expr: List[str]) -> List[int]:
        return [sym_index[t] for t in expr]

    # Split assertions into chunks.
    total = len(assertions)
    chunks: List[List[Dict[str, object]]] = []
    for i in range(0, total, chunk_size):
        chunks.append(assertions[i : i + chunk_size])

    out_path.parent.mkdir(parents=True, exist_ok=True)

    chunk_dir = out_path.parent / out_path.stem
    chunk_dir.mkdir(parents=True, exist_ok=True)

    # Emit each chunk module.
    for ci, chunk in enumerate(chunks):
        chunk_mod = f"{module_name}.Chunk{ci:04d}"
        chunk_path = chunk_dir / f"Chunk{ci:04d}.agda"

        premises_rows: List[List[List[int]]] = []
        concl_rows: List[List[int]] = []
        label_rows: List[str] = []

        for li, a in enumerate(chunk):
            owner = f"chunk[{ci}][{li}]"
            label_rows.append(str(_require_field(a, "label", owner)))
            concl_rows.append(enc(_expect_str_list(_require_field(a, "expr", owner), f"{owner}['expr']")))

            premises: List[List[int]] = []
            for flbl in _expect_str_list(_require_field(a, "float_hyps", owner), f"{owner}['float_hyps']"):
                premises.append(enc(_floating_formula(floating, flbl, "db['floating']")))
            for elbl in _expect_str_list(_require_field(a, "ess_hyps", owner), f"{owner}['ess_hyps']"):
                premises.append(enc(_essential_expr(essential, elbl, "db['essential']")))
            premises_rows.append(premises)

        lines: List[str] = []
        lines.append("{-")
        lines.append("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI")
        lines.append("Copyright (C) 2026 AI.IMPACT GmbH")
        lines.append("SPDX-License-Identifier: GPL-3.0-only")
        lines.append("-}")
        lines.append("")
        lines.append("{-# OPTIONS --safe #-}")
        lines.append(f"module {chunk_mod} where")
        lines.append("")
        lines.append("open import LogOS.Prelude")
        lines.append("open import LogOS.Prelude.List using (List; []; _∷_)")
        lines.append("")
        lines.append("-- Formulas are token lists (symbols are interned as Nat indices).")
        lines.append("Formula : Set")
        lines.append("Formula = List ℕ")
        lines.append("")
        lines.append("-- Local assertion index -> original Metamath label.")
        start = ci * chunk_size
        lines.append(f"-- Global start index: {start}")
        for li, lab in enumerate(label_rows):
            lines.append(f"-- {li}: {lab}")
        lines.append("")
        lines.append("premisesTable : List (List Formula)")
        lines.append(f"premisesTable = {_agda_list_list_formula(premises_rows)}")
        lines.append("")
        lines.append("conclTable : List Formula")
        lines.append(f"conclTable = {_agda_list_formula(concl_rows)}")
        lines.append("")
        lines.append("lookup : ∀ {A : Set} → ℕ → List A → A → A")
        lines.append("lookup zero (x ∷ xs) d = x")
        lines.append("lookup (suc n) (x ∷ xs) d = lookup n xs d")
        lines.append("lookup _ [] d = d")
        lines.append("")
        lines.append("hypsL : ℕ → List Formula")
        lines.append("hypsL n = lookup n premisesTable []")
        lines.append("")
        lines.append("conclL : ℕ → Formula")
        lines.append("conclL n = lookup n conclTable []")
        lines.append("")

        chunk_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    # Emit aggregator module.
    lines = []
    lines.append("{-")
    lines.append("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI")
    lines.append("Copyright (C) 2026 AI.IMPACT GmbH")
    lines.append("SPDX-License-Identifier: GPL-3.0-only")
    lines.append("-}")
    lines.append("")
    lines.append("{-# OPTIONS --safe #-}")
    lines.append(f"module {module_name} where")
    lines.append("")
    lines.append("open import LogOS.Prelude")
    lines.append("open import LogOS.Prelude.List using (List; []; _∷_)")
    lines.append("")
    lines.append("import LogOS.Ports.Metamath as MM")
    lines.append("")
    lines.append("-- Formulas are token lists (symbols are interned as Nat indices).")
    lines.append("Formula : Set")
    lines.append("Formula = List ℕ")
    lines.append("")
    lines.append("numSymbols : ℕ")
    lines.append(f"numSymbols = {len(syms)}")
    lines.append("")
    lines.append("numAssertions : ℕ")
    lines.append(f"numAssertions = {total}")
    lines.append("")
    lines.append("chunkSize : ℕ")
    lines.append(f"chunkSize = {chunk_size}")
    lines.append("")
    lines.append("numChunks : ℕ")
    lines.append(f"numChunks = {len(chunks)}")
    lines.append("")
    lines.append(f"-- Assertions: {total} (chunk size {chunk_size}, chunks {len(chunks)})")
    lines.append("")
    lines.append("-- Symbol table (index -> original token).")
    for i, s in enumerate(syms):
        lines.append(f"-- {i}: {s}")
    lines.append("")

    for ci in range(len(chunks)):
        lines.append(f"import {module_name}.Chunk{ci:04d} as C{ci:04d}")
    lines.append("")

    lines.append("-- Labels are (chunk-index, local-index).")
    lines.append("Label : Set")
    lines.append("Label = ℕ × ℕ")
    lines.append("")

    lines.append("hyps : Label → List Formula")
    for ci in range(len(chunks)):
        pat = _agda_nat_pat(ci)
        lines.append(f"hyps ({pat} , n) = C{ci:04d}.hypsL n")
    lines.append("hyps (_ , _) = []")
    lines.append("")

    lines.append("concl : Label → Formula")
    for ci in range(len(chunks)):
        pat = _agda_nat_pat(ci)
        lines.append(f"concl ({pat} , n) = C{ci:04d}.conclL n")
    lines.append("concl (_ , _) = []")
    lines.append("")

    lines.append("DB : MM.Database Formula")
    lines.append("DB = record { Label = Label ; hyps = hyps ; concl = concl }")
    lines.append("")
    lines.append("-- Derived: closure transformer for this database.")
    lines.append("module Closed = MM.FromDB DB")
    lines.append("")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def emit_agda_hs_runner(
    out_path: Path,
    *,
    module_name: str,
    db_module: str,
) -> None:
    # This is intentionally not `--safe`: it contains a small, explicit FFI bridge
    # used only for running a compiled demo binary (kept under `_build/`).
    out_path.parent.mkdir(parents=True, exist_ok=True)

    lines: List[str] = []
    lines.append("{-")
    lines.append("LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI")
    lines.append("Copyright (C) 2026 AI.IMPACT GmbH")
    lines.append("SPDX-License-Identifier: GPL-3.0-only")
    lines.append("-}")
    lines.append("")
    lines.append(f"module {module_name} where")
    lines.append("")
    lines.append("open import Agda.Builtin.IO using (IO)")
    lines.append("open import Agda.Builtin.Unit using (⊤)")
    lines.append("open import Agda.Builtin.String using (String; primStringAppend; primShowNat)")
    lines.append("")
    lines.append(f"import {db_module} as DB")
    lines.append("")
    lines.append("infixr 5 _++_")
    lines.append("_++_ : String → String → String")
    lines.append("_++_ = primStringAppend")
    lines.append("")
    lines.append("postulate")
    lines.append("  putStrLn : String → IO ⊤")
    lines.append("")
    lines.append("{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}")
    lines.append("{-# COMPILE GHC putStrLn = TIO.putStrLn #-}")
    lines.append("")
    lines.append("msg : String")
    lines.append(
        "msg = \"symbols: \" ++ primShowNat DB.numSymbols ++ \", assertions: \" ++ primShowNat DB.numAssertions"
    )
    lines.append("")
    lines.append("main : IO ⊤")
    lines.append("main = putStrLn msg")
    lines.append("")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
