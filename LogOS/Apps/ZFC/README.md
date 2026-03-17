<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS.Apps.ZFC

Detailed pack story for the ZFC application lane.

## Goal

Present ZF/ZFC as an application pack whose primary interface is a stack of
logical transformers (`View`s) with one shared, explicit boundary:
sets-as-predicates with refinement by entailment.

## Entrypoints

- `LogOS/Apps/ZFC/All.agda`
- `LogOS/Apps/ZFC/Stack.agda`
- `LogOS/Apps/ZFC/Proof.agda`
- `LogOS/Apps/ZFC/Stack/ReifiedTower.agda`
- `LogOS/Apps/ZFC/SetTheory/Definable.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`

## Implemented now

- Stack-first ZF/ZFC constructor interface, where constructors are literal
  `View`s into the set boundary and composition is literal `View` composition.
- Explicit profile towers for Separation, Replacement, and Choice.
- Asymptotic reification pattern and curated packaging via `ReifiedTower`.
- Stage-indexed admissibility wrapper for reification, including the
  iterative-tree hierarchy ladder and the same-stage late-collapse assembler.
- Canonical FO representability and successor small-truth lift over the
  iterative-tree base layer.
- Cumulative-hierarchy tower packaging and theorem-facing canonical bridge
  facades.
- Curated iterative-tree semantic entrypoint with canonical slice/bridge names
  and optional completion adapters.
- First-order proof layer, Metamath bridge, and well-founded-part transformer.

## Planned

- Further concrete reification instances and closures beyond the iterative-set-tree base layer,
  while keeping all additional assumptions explicit and locally scoped.

## Local map

- `Stack/**`: reusable ZFC stack packaging
- `Models/IterativeSetTree/**`: concrete iterative-tree semantics
- `Proof/**`: first-order proof and soundness layer
- `Metamath/**`: parsing and roundtrip bridge
