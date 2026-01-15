<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Curry-Howard-Lambek - LogOS (Capstone View)

```agda
{-# OPTIONS --safe #-}
module docs.Views.CurryHowardLambek where

open import LogOS.Docs.Views.View_CurryHowardLambek public
```

This note states the **CHL capstone** of the LogOS kernel. It is deliberately
preorder-safe and proof-relevant: everything is up to refinement/observational
equivalence, not definitional equality.

Theorem spine (authoritative)
-----------------------------
- `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `CHL`):
  `capstone`, `capstone-complete`, `capstone-complete-budget`,
  `completeF`, `completeF-budget`, `formula-program`.
- Commuting square with the institution view:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Commuting`),
  `formula-sat-boundary`.
- Projection certificate:
  `LogOS/Theorems/Meta/CHL/ViewTheorems.agda` (`For …` → `Projections`),
  `projection`.
- The prose below is explanatory; the statements above are the authoritative claims.

Exact claims (all kernel-native):

- *proof theory:* proofs/programs are refinement steps on `Code`, with cut/identity
  inherited from the preorder (`LogOS/Theorems/Meta/CHL/Definition.agda`).
- *model theory:* refinement implies entailment at the H-tier and the boundary
  tier (`LogOS/Theorems/Meta/CHL/ModelTheory.agda`).
- *category theory:* codes form a thin category and `FlowCode` is a monotone
  endofunctor (`LogOS/Theorems/Meta/CHL/Category.agda`).
- *observer semantics:* guarded truth is stability under the operational step
  (`FlowCode`), exposed via the CHL guarded view (`LogOS/Theorems/Meta/CHL/Guarded.agda`).
- *interoperability:* port translations are meaning-preserving at the boundary
  (`LogOS/Theorems/Meta/CHL/Interoperability.agda`).
- *strict syntax as port input:* strict formulas transpile to any boundary port
  via the canonical interlingua (`LogOS/Theorems/Meta/CHL/Interoperability.agda` → `Strict`,
  with `Strict.Transpiler.compile-transpiler`).
- *code as port input:* kernel code transpiles to any boundary port, uniquely up
  to boundary satisfaction (`LogOS/Theorems/Meta/CHL/Interoperability.agda` → `Code`,
  with `Code.Transpiler.compile-transpiler`).
- *indexed view:* signature reindexing preserves code/refinement; with strict
  syntax translation this remains literal (`LogOS/Theorems/Meta/CHL/ViewTheorems.agda` → `ReindexWithFml`).

What this does **not** claim:
- No antisymmetry or proof-irrelevance is assumed; refinement is directed.
- No global completeness for strict syntax is claimed without explicit adequacy.
- No claim that every boundary constraint is denoted by a formula (`TransH` is
  not assumed surjective).

Relative completeness for strict formulas is available under a local
boundary-adequacy assumption (order reflection on the image of `to∂`):

- `LogOS/Theorems/Meta/CHL/SyntaxCompleteness.agda`

Boundary-level completeness for the code preorder (on the image of `to∂`) is
packaged separately:

- `LogOS/Theorems/Meta/CHL/Completeness.agda`

Budgeted adequacy (completeness relative to a resource/budget predicate on
observations) is supported with dedicated statements:

- `LogOS/Theorems/Meta/CHL/Completeness.agda`
- `LogOS/Theorems/Meta/CHL/SyntaxCompleteness.agda`
- Kernel-aligned budget predicate from telemetry:
  `LogOS/Boundary/Budget.agda`

Budgeted story in one sentence: choose a budget predicate `B`, assume
`BudgetedAdequacy B`, then you get code-level completeness, strict-syntax
completeness, and formula completeness (`completeF-budget`) all at once.

Concept flow (kernel‑aligned):
- Pick a telemetry port for boundary programs (`LogOS/Boundary/Telemetry.agda`).
- Choose a trace budget `b` on the telemetry trace carrier.
- Define `B = budget-from-trace b` from `LogOS/Boundary/Budget.agda`.
- Assume `BudgetedAdequacy B` and apply `sound-complete∂-budget`,
  `sound-completeS-budget`, and `completeF-budget`.

The single bundled capstone theorem (soundness + bundled views, with optional
completeness under adequacy) is:

- `LogOS/Theorems/Meta/CHL/Capstone.agda`

Optional proof-theory packaging (Hilbert-style, Imp external, Box = FlowCode):

- `LogOS/Theorems/Meta/CHL/ProofTheory.agda`

Canonical definitions of propositions, types, proofs, and programs:

- `LogOS/Theorems/Meta/CHL/Definition.agda`
