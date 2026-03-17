#!/usr/bin/env python3
# LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Tuple


@dataclass(frozen=True)
class FloatingHyp:
    label: str
    typecode: str
    var: str


@dataclass(frozen=True)
class EssentialHyp:
    label: str
    expr: List[str]


@dataclass
class Assertion:
    label: str
    kind: str  # "a" or "p"
    expr: List[str]
    float_hyps: List[str]  # labels (mandatory, in order)
    ess_hyps: List[str]  # labels (mandatory, in order)
    disjoint_pairs: List[Tuple[str, str]]  # (x,y) with x < y
    proof_len: int
    proof: Optional[List[str]]  # proof tokens (optional)

