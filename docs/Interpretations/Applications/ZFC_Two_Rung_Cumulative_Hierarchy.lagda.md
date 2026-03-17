<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZFC: A Two-Rung Cumulative Hierarchy Slice

This note states the iterative-tree ZFC result in the precise shape the code now
proves.

It does **not** claim a full global cumulative hierarchy, and it does **not**
claim same-stage unrestricted comprehension.

It states the sharper theorem:

- one coherent hierarchy section determines a canonical successor slice,
- that slice contains a canonical cross-stage Separation/Replacement bridge,
- same-stage proof models at the lower and successor rungs appear only after
  explicit local completion data are supplied at those rungs.

Read this note in exactly that order:

1. canonical slice
2. canonical bridge
3. optional local completion

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Applications.ZFC_Two_Rung_Cumulative_Hierarchy where

import LogOS.API.LT
```

Statement
---------

Fix:

- a hierarchy section `H : HierarchySectionᵛ`,
- a base level `ℓ`,
- optional lower-rung completion data
  `A₀ : CurrentCompletion` at the chosen `H` and `ℓ`,
- optional successor-rung completion data
  `A₁ : SuccessorCompletion` at the chosen `H` and `ℓ`.

Then the canonical surface module
`LogOS.Apps.ZFC.Models.IterativeSetTree.TwoRungSliceSurface.TwoRungSlice H {ℓ}`
exposes two different layers of result.

Canonical bridge layer
----------------------

From `H` and `ℓ` alone, the slice already provides:

- `S.currentBase` : the canonical lower-rung ZF base,
- `S.successorBase` : the canonical successor-rung ZF base,
- `B.separationSet↑ P ρ x` : the canonical successor-stage set representing the
  lower-stage definable subset of `x`,
- `B.replacementSet↑ R₀ ρ (x , fun)` : the canonical successor-stage set
  representing the lower-stage definable image of `x` under the functional
  relation `R₀`.

The bridge-facing names `separationSet↑`, `replacementSet↑`,
`separation-schema↑`, and `replacement-schema↑` are generic stack-level names
coming from `LogOS/Apps/ZFC/Stack/AsymptoticReification/SuccessorBridge.agda`;
`ITCanon.BridgeForLevel` is the iterative-tree instantiation.

The correctness theorems are:

- `B.separation-schema↑`
- `B.replacement-schema↑`

Informally:

- `lift z ∈ B.separationSet↑ P ρ x` iff `z ∈ x` and `P(z , x , ρ)` holds on the
  lower rung,
- `lift z ∈ B.replacementSet↑ R₀ ρ (x , fun)` iff there exists `u ∈ x` such that
  `R₀(u , z , ρ)` holds on the lower rung, under the explicit functionality
  witness `fun`.

Local completion layer
----------------------

Same-stage proof models are deliberately **not** part of the canonical bridge.
They appear only after explicit local completion data are supplied:

- `Current A₀ .currentModel`
- `Successor A₁ .successorModel`

This is the precise type-level separation between:

- canonical hierarchy transport, and
- non-canonical same-stage completion.

Why this is the right theorem
-----------------------------

This is the internal LogOS translation of the textbook cumulative-hierarchy
intuition:

- lower rung = the stage whose sets you quantify over,
- successor rung = the stage where lower-stage definable subsets and lower-stage
  definable images live.

What matters is that the stage shift is explicit. The raw iterative-tree
presentation still does not force same-stage FO comprehension. The code proves
the precise structural fact: lower-stage definability becomes successor-stage sethood.

What remains external
---------------------

The slice still depends on explicit assumption surfaces from
`LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`:

- `Extensionalityᵛ`
- `PowersetStructureᵛ`
- structural `Choice`
- structural `EmptyOrElemUpgrade`

Those are not hidden. That is deliberate.

Pointers
--------

- `LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/HierarchyCore.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/CanonicalBridge.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/SuccessorTruthLift.agda`
- `docs/Interpretations/Applications/ZFC_Curated_Surface.lagda.md`
- `docs/Interpretations/Orientation/ZFC_Quickstart.lagda.md`
