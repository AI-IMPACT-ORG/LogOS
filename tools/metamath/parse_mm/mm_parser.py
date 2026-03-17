#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from mm_error import MMError
from mm_model import Assertion, EssentialHyp, FloatingHyp
from mm_tokens import _TokenStack, _read_until


def _pairs(vars_: List[str]) -> List[Tuple[str, str]]:
    out: List[Tuple[str, str]] = []
    n = len(vars_)
    for i in range(n):
        for j in range(i + 1, n):
            a, b = vars_[i], vars_[j]
            out.append((a, b) if a < b else (b, a))
    return out


def parse_mm(
    root: Path,
    *,
    include_proofs: bool,
    max_assertions: Optional[int],
    check_proofs: bool = False,
    progress_every: Optional[int] = None,
) -> Dict[str, object]:
    ts = _TokenStack(root)

    constants: Set[str] = set()
    variables: Set[str] = set()

    floating: Dict[str, FloatingHyp] = {}
    essential: Dict[str, EssentialHyp] = {}

    # Active scope stacks, with length markers for ${ ... $}.
    active_f: List[FloatingHyp] = []
    active_e: List[EssentialHyp] = []
    active_d: List[List[str]] = []  # raw var lists from $d
    markers: List[Tuple[int, int, int]] = []

    assertions: List[Assertion] = []
    assertion_count = 0
    stopped_early = False

    # Proven/usable assertions so far (axioms + checked theorems).
    assertion_by_label: Dict[str, Assertion] = {}

    def push_scope() -> None:
        markers.append((len(active_f), len(active_e), len(active_d)))

    def pop_scope() -> None:
        if not markers:
            raise MMError("unmatched $} (scope underflow)")
        lf, le, ld = markers.pop()
        del active_f[lf:]
        del active_e[le:]
        del active_d[ld:]

    def mandatory_vars_for(expr: List[str], ess_hyps: List[EssentialHyp]) -> Set[str]:
        mv: Set[str] = set()
        for t in expr:
            if t in variables:
                mv.add(t)
        for h in ess_hyps:
            for t in h.expr:
                if t in variables:
                    mv.add(t)
        return mv

    def ensure_declared_expr(expr: List[str], *, where: str) -> None:
        if not expr:
            raise MMError(f"empty expression in {where}")
        tc = expr[0]
        if tc not in constants:
            raise MMError(f"expression typecode {tc!r} is not a declared constant ({where})")
        for t in expr[1:]:
            if t in constants or t in variables:
                continue
            raise MMError(f"unknown symbol {t!r} in expression ({where})")

    def subst_expr(expr: List[str], subst: Dict[str, List[str]]) -> List[str]:
        out: List[str] = []
        for t in expr:
            if t in subst:
                out.extend(subst[t])
            else:
                out.append(t)
        return out

    def check_disjoint(subst: Dict[str, List[str]], pairs: List[Tuple[str, str]]) -> None:
        for (x, y) in pairs:
            sx = subst.get(x)
            sy = subst.get(y)
            if sx is None or sy is None:
                # Disjointness only applies to mandatory variables; if missing we treat as error.
                raise MMError(f"DV pair refers to missing substitution var: {x},{y}")
            vx = {t for t in sx if t in variables}
            vy = {t for t in sy if t in variables}
            if vx & vy:
                common = sorted(vx & vy)
                raise MMError(f"DV violation: {x},{y} share {common}")

    def apply_assertion(label: str, args: List[List[str]]) -> List[str]:
        a = assertion_by_label.get(label)
        if a is None:
            raise MMError(f"unknown or not-yet-proved assertion label in proof: {label}")

        num_f = len(a.float_hyps)
        num_e = len(a.ess_hyps)
        if len(args) != num_f + num_e:
            raise MMError(
                f"arity mismatch applying {label}: need {num_f + num_e} hyps, got {len(args)}"
            )

        subst: Dict[str, List[str]] = {}

        # 1) Floating hypotheses determine substitution.
        for i, flbl in enumerate(a.float_hyps):
            fh = floating.get(flbl)
            if fh is None:
                raise MMError(f"missing $f hypothesis {flbl} referenced by {label}")
            want_tc = fh.typecode
            want_var = fh.var

            got = args[i]
            if not got:
                raise MMError(f"empty expression used for floating hyp {flbl} of {label}")
            got_tc = got[0]
            if got_tc != want_tc:
                raise MMError(
                    f"typecode mismatch for {label}/{flbl}: want {want_tc}, got {got_tc}"
                )
            rhs = got[1:]
            prev = subst.get(want_var)
            if prev is None:
                subst[want_var] = rhs
            elif prev != rhs:
                raise MMError(
                    f"inconsistent substitution for {want_var} applying {label}: {prev} vs {rhs}"
                )

        # 2) Disjoint variable restrictions.
        check_disjoint(subst, a.disjoint_pairs)

        # 3) Essential hypotheses must match after substitution.
        for j, elbl in enumerate(a.ess_hyps):
            templ = essential.get(elbl)
            if templ is None:
                raise MMError(f"missing $e hypothesis {elbl} referenced by {label}")
            got = args[num_f + j]
            want = subst_expr(templ.expr, subst)
            if got != want:
                raise MMError(f"essential hyp mismatch for {label}/{elbl}: got {got}, want {want}")

        # 4) Produce substituted conclusion.
        return subst_expr(a.expr, subst)

    def decode_compressed(theorem: Assertion, proof_tokens: List[str]) -> List[object]:
        # Returns a list of steps: either str(label) or ("saved", idx).
        if not proof_tokens or proof_tokens[0] != "(":
            raise MMError("not a compressed proof (expected leading '(')")

        # Parse label list between (...) and concatenate the code afterwards.
        labels: List[str] = []
        i = 1
        while i < len(proof_tokens) and proof_tokens[i] != ")":
            labels.append(proof_tokens[i])
            i += 1
        if i >= len(proof_tokens) or proof_tokens[i] != ")":
            raise MMError("compressed proof missing closing ')'")
        i += 1

        code = "".join(proof_tokens[i:])
        if "?" in code:
            raise MMError("compressed proof contains '?' (incomplete proof)")

        ref = theorem.float_hyps + theorem.ess_hyps + labels

        steps: List[object] = []
        acc = 0
        for ch in code:
            if ch == "Z":
                if acc != 0:
                    raise MMError("compressed proof has 'Z' inside an encoded number")
                steps.append(("save", None))
                continue

            o = ord(ch)
            if ord("U") <= o <= ord("Y"):
                # Metamath compressed proofs use base-5 digits 1..5 encoded as U..Y.
                acc = acc * 5 + (o - ord("U") + 1)
                continue
            if ord("A") <= o <= ord("T"):
                n = acc * 20 + (o - ord("A") + 1)
                acc = 0
                if n <= 0:
                    raise MMError("decoded nonpositive proof reference")
                # Map to ref or saved slot.
                if n <= len(ref):
                    steps.append(ref[n - 1])
                else:
                    steps.append(("saved", n - len(ref) - 1))
                continue

            raise MMError(f"invalid compressed proof character: {ch!r}")

        if acc != 0:
            raise MMError("dangling compressed proof accumulator (missing A..T terminator?)")

        return steps

    def check_proof(theorem: Assertion, proof_tokens: List[str]) -> None:
        # Hypothesis labels allowed in this theorem's proof.
        hyp_labels = set(theorem.float_hyps + theorem.ess_hyps)

        # Turn into a stream of steps.
        if proof_tokens and proof_tokens[0] == "(":
            steps = decode_compressed(theorem, proof_tokens)
        else:
            steps = list(proof_tokens)

        stack: List[List[str]] = []
        saved: List[List[str]] = []

        def push(expr: List[str]) -> None:
            stack.append(expr)

        def popn(n: int) -> List[List[str]]:
            if n < 0:
                raise MMError("internal: negative pop")
            if len(stack) < n:
                raise MMError(f"stack underflow: need {n}, have {len(stack)}")
            if n == 0:
                return []
            out = stack[-n:]
            del stack[-n:]
            return out

        for st in steps:
            if isinstance(st, tuple):
                tag = st[0]
                if tag == "save":
                    if not stack:
                        raise MMError("save (Z) with empty stack")
                    saved.append(stack[-1])
                    continue
                if tag == "saved":
                    idx = int(st[1])
                    if idx < 0 or idx >= len(saved):
                        raise MMError(f"saved ref out of range: {idx} (have {len(saved)})")
                    push(saved[idx])
                    continue
                raise MMError(f"unknown internal step tag: {tag}")

            label = str(st)
            if label in hyp_labels:
                # Push the hypothesis expression.
                if label in floating:
                    fh = floating[label]
                    push([fh.typecode, fh.var])
                elif label in essential:
                    push(essential[label].expr)
                else:
                    raise MMError(f"hypothesis label not found as $f/$e: {label}")
                continue

            # Disallow using $f/$e outside the hypothesis list (scope discipline).
            if label in floating or label in essential:
                raise MMError(f"out-of-scope hypothesis used in proof of {theorem.label}: {label}")

            a = assertion_by_label.get(label)
            if a is None:
                raise MMError(f"unknown/assertion label in proof of {theorem.label}: {label}")

            arity = len(a.float_hyps) + len(a.ess_hyps)
            args = popn(arity)
            args = list(args)  # in stack order
            concl = apply_assertion(label, args)
            push(concl)

        if len(stack) != 1:
            raise MMError(f"proof of {theorem.label} leaves stack size {len(stack)} (expected 1)")
        if stack[0] != theorem.expr:
            raise MMError(f"proof of {theorem.label} proves {stack[0]} but theorem is {theorem.expr}")

    while True:
        try:
            tok = ts.pop()
        except StopIteration:
            break

        if tok == "${":
            push_scope()
            continue
        if tok == "$}":
            pop_scope()
            continue

        if tok == "$c":
            syms = _read_until(ts, "$.")
            for s in syms:
                if s in variables:
                    raise MMError(f"symbol declared as both $v and $c: {s}")
                constants.add(s)
            continue

        if tok == "$v":
            syms = _read_until(ts, "$.")
            for s in syms:
                if s in constants:
                    raise MMError(f"symbol declared as both $c and $v: {s}")
                variables.add(s)
            continue

        if tok == "$d":
            vs = _read_until(ts, "$.")
            for v in vs:
                if v not in variables:
                    raise MMError(f"$d lists non-variable symbol {v!r}")
            active_d.append(vs)
            continue

        if tok in ("$t", "$j"):
            # Typesetting / auxiliary metadata: ignore.
            _read_until(ts, "$.")
            continue

        # Labelled statement.
        label = tok
        try:
            stype = ts.pop()
        except StopIteration as e:
            raise MMError(f"unexpected EOF after label {label}") from e

        if stype == "$f":
            body = _read_until(ts, "$.")
            if len(body) != 2:
                raise MMError(
                    f"malformed $f statement {label}: expected 2 tokens, got {len(body)}"
                )
            if body[0] not in constants:
                raise MMError(
                    f"$f typecode {body[0]!r} is not a declared constant (label {label})"
                )
            if body[1] not in variables:
                raise MMError(
                    f"$f variable {body[1]!r} is not a declared variable (label {label})"
                )
            fh = FloatingHyp(label=label, typecode=body[0], var=body[1])
            if label in floating:
                raise MMError(f"duplicate floating hyp label: {label}")
            floating[label] = fh
            active_f.append(fh)
            continue

        if stype == "$e":
            expr = _read_until(ts, "$.")
            ensure_declared_expr(expr, where=f"$e {label}")
            eh = EssentialHyp(label=label, expr=expr)
            if label in essential:
                raise MMError(f"duplicate essential hyp label: {label}")
            essential[label] = eh
            active_e.append(eh)
            continue

        if stype == "$a":
            expr = _read_until(ts, "$.")
            ensure_declared_expr(expr, where=f"$a {label}")
            mv = mandatory_vars_for(expr, active_e)
            mand_f = [fh.label for fh in active_f if fh.var in mv]
            mand_e = [eh.label for eh in active_e]

            d_pairs: Set[Tuple[str, str]] = set()
            for vs in active_d:
                scoped = [v for v in vs if v in mv]
                for p in _pairs(scoped):
                    d_pairs.add(p)

            assertions.append(
                Assertion(
                    label=label,
                    kind="a",
                    expr=expr,
                    float_hyps=mand_f,
                    ess_hyps=mand_e,
                    disjoint_pairs=sorted(d_pairs),
                    proof_len=0,
                    proof=None,
                )
            )
            assertion_by_label[label] = assertions[-1]
            assertion_count += 1
            if max_assertions is not None and assertion_count >= max_assertions:
                stopped_early = True
                break
            continue

        if stype == "$p":
            expr: List[str] = []
            while True:
                t = ts.pop()
                if t == "$=":
                    break
                expr.append(t)
            ensure_declared_expr(expr, where=f"$p {label}")

            proof_len = 0
            proof: Optional[List[str]] = [] if include_proofs else None
            proof_for_check: Optional[List[str]] = [] if check_proofs else None
            while True:
                t = ts.pop()
                if t == "$.":
                    break
                proof_len += 1
                if include_proofs:
                    assert proof is not None
                    proof.append(t)
                if check_proofs:
                    assert proof_for_check is not None
                    proof_for_check.append(t)

            mv = mandatory_vars_for(expr, active_e)
            mand_f = [fh.label for fh in active_f if fh.var in mv]
            mand_e = [eh.label for eh in active_e]

            d_pairs: Set[Tuple[str, str]] = set()
            for vs in active_d:
                scoped = [v for v in vs if v in mv]
                for p in _pairs(scoped):
                    d_pairs.add(p)

            assertions.append(
                Assertion(
                    label=label,
                    kind="p",
                    expr=expr,
                    float_hyps=mand_f,
                    ess_hyps=mand_e,
                    disjoint_pairs=sorted(d_pairs),
                    proof_len=proof_len,
                    proof=proof,
                )
            )

            # Check the proof before making this theorem available to later proofs.
            thm = assertions[-1]
            if check_proofs:
                if proof_for_check is None:
                    raise MMError("internal: missing proof token stream for checking")
                check_proof(thm, proof_for_check)

            assertion_by_label[label] = thm
            assertion_count += 1
            if max_assertions is not None and assertion_count >= max_assertions:
                stopped_early = True
                break
            if progress_every is not None and assertion_count % progress_every == 0:
                num_a = sum(1 for a in assertions if a.kind == "a")
                num_p = sum(1 for a in assertions if a.kind == "p")
                print(
                    f"... {assertion_count} assertions ({num_a} $a, {num_p} $p); latest: {label}",
                    file=sys.stderr,
                )
            continue

        raise MMError(f"unknown statement type after {label}: {stype}")

    if markers and not stopped_early:
        raise MMError(f"unclosed scopes at EOF: {len(markers)}")

    num_a = sum(1 for a in assertions if a.kind == "a")
    num_p = sum(1 for a in assertions if a.kind == "p")

    return {
        "root": str(root),
        "constants": sorted(constants),
        "variables": sorted(variables),
        "floating": {k: {"typecode": v.typecode, "var": v.var} for k, v in floating.items()},
        "essential": {k: v.expr for k, v in essential.items()},
        "assertions": [
            {
                "label": a.label,
                "kind": a.kind,
                "expr": a.expr,
                "float_hyps": a.float_hyps,
                "ess_hyps": a.ess_hyps,
                "disjoint_pairs": [[x, y] for (x, y) in a.disjoint_pairs],
                "proof_len": a.proof_len,
                "proof": a.proof,
            }
            for a in assertions
        ],
        "stats": {
            "num_constants": len(constants),
            "num_variables": len(variables),
            "num_floating": len(floating),
            "num_essential": len(essential),
            "num_assertions": len(assertions),
            "num_a": num_a,
            "num_p": num_p,
        },
    }
