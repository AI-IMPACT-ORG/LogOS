<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZF/ZFC Quickstart (stack-first, reification-first)

This is a minimal, typechecked walkthrough of the intended v1.1 user story for
the ZFC pack:

- start from an explicit **set boundary** (`SetContext`),
- assume a boundary-level **reification doctrine** up to a chosen `Flow` (admissibility-gated),
- make stability + any remaining set-theoretic strength explicit as ledger fields, and
- obtain a first-order ZFC model surface (`ZFCStackFO`) suitable for definability and proof semantics.

Safety note (pedantic)
----------------------

In v1.1 the predicate reification port is **restricted-by-default**:
reifying a predicate requires explicit evidence that it is *admitted*
(`Reifiable P`). This is a deliberate LOGᴳ discipline choice: it prevents
accidentally assuming a form of unbounded comprehension.

For experiments, there is a separate, explicit *total/unrestricted* wrapper
(`TotalPredicateReification`). This wrapper is the one that bridges to
`QuotePort` (see `LogOS/Apps/ZFC/Stack/ReificationAsQuotePort.agda`), and it is
**not** “safe for free”: combining total reification with `Flow = id` (e.g.
`idClosure`) admits Russell-style diagonalisation.

If you want a cumulative-hierarchy or rank-bounded story without changing the
downstream ZFC tower, the intended interface is the staged wrapper
`StagedPredicateReification`: staged admissibility is the primitive interface,
it forgets to an ordinary restricted `PredicateReification`, and the
total/unrestricted wrapper is recoverable only if you separately provide a
stage-totality witness. The stage carrier itself is now LT-level
(`stageCP : ConPreorder ... ...`), not a ZFC-local preorder record.

Audit pointers
--------------

- Audit workflow: `docs/Core/Orientation/Audit_Guide.lagda.md`
- ZFC upgrade index (generated): `docs/Generated/ZFC_Upgrade_Index.md`
- ZFC pack entrypoints: `LogOS/Apps/ZFC/Stack.agda`, `LogOS/Apps/ZFC/All.agda`
- Closure/flow doctrine: `LogOS/LT/Flow.agda`
- Design-target spec (kernel/flow story): `docs/Core/Spec/LogicalTransformers.lagda.md`

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Orientation.ZFC_Quickstart where

open import LogOS.API.LT

-- Primary stack-first interface.
open import LogOS.Apps.ZFC.Stack
import LogOS.Apps.ZFC.Stack.ZFCore as ZFCore

-- Formula-driven definable Separation/Replacement over `ZFCStackFO`.
open import LogOS.Apps.ZFC.SetTheory.Definable

open import LogOS.Apps.ZFC.Proof.Syntax using (Formula; var; _∈F_; _≈F_)
```

From a reification ledger to a first-order ZFC model
---------------------------------------------------

The public semantic story now has three exposed surfaces:

1. `Canonical.ForLevel H {ℓ}` gives the canonical two-rung slice.
2. `Canonical.BridgeForLevel H {ℓ}` exposes the theorem-facing cross-stage bridge inside that slice.
3. `Completion.ForLevel H {ℓ}` adds same-stage proof-model completion.

That order matters. The slice and bridge are canonical once the hierarchy
section is fixed; the proof model is not.

`Stack.ReifiedTower` packages the reification/stability story into an explicit
ledger record; it does **not** claim that the ledger fields are derivable from
LogOS kernel primitives alone.

```agda
import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.ReifiedTower as RT

module ReificationLedger {ℓ : Level}
  (C : ZFCore.SetContext {ℓ})
  (R : AR.PredicateReification C)
  (L : RT.ReifiedZFCFO C R)
  where

  open RT.ReifiedZFCFO L

  model : _
  model = stackFO
```

Optional: build that restricted ledger from a stage-indexed admissibility layer
------------------------------------------------------------------------

This is the "late collapse" path: expose only stage-admitted predicates to the
ZFC tower, and forget stage indices once you enter the ordinary restricted
reification ledger.

The first concrete base layer in v1.1 lives at
`LogOS/Apps/ZFC/Models/IterativeSetTree/StagedReification.agda`: it uses the
iterative-set-tree rank as stage data, and keeps the two raw-tree non-forced
gaps explicit as assumptions:

- `Extensionalityᵛ`: needed to turn membership-derived `_≈_` back into
  definitional equality for the raw tree presentation.
- `PowersetStructureᵛ`: needed because full powerset is not derivable
  predicatively from the raw tree carrier alone.

The curated semantic entrypoint is now
`LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`. It packages the
late-collapse route into the namespaced surfaces:

- `HierarchySectionᵛ`
- `Canonical.ForLevel`
- `Canonical.BridgeForLevel`
- `Completion.ForLevel`

This is the important split:

- `Canonical.ForLevel H {ℓ}` gives the **canonical** two-rung slice cut from one
  hierarchy section `H`,
- `Canonical.BridgeForLevel H {ℓ}` gives the theorem-facing cross-stage
  Separation/Replacement bridge,
- `Completion.ForLevel H {ℓ}` adds same-stage proof models only after explicit
  completion data are supplied.

The stage shift is now the explicit FO boundary: lower-stage formulas become
successor-stage classifiers, so cross-stage Separation/Replacement are
canonical inside the slice, while same-stage completion remains optional and
local.

The remaining assumption surfaces also stay explicit:

- `Extensionalityᵛ`
- `PowersetStructureᵛ`
- the small Separation classifier family in `FORepresentabilityᵛ` when you insist on raw-stage or same-stage FO witnesses
- structural `Choice`
- structural `EmptyOrElemUpgrade`

Pedantically: inside the canonical successor-stage bridge, the raw-stage
Separation classifier disappears one stage up. It remains explicit only when
you ask for raw-stage or same-stage FO reification before taking that stage
step.

If you want the precise theorem statement for that split, read:

- `docs/Interpretations/Applications/ZFC_Two_Rung_Cumulative_Hierarchy.lagda.md`
- `docs/Interpretations/Applications/ZFC_Curated_Surface.lagda.md`

This now lines up directly with the central LT vocabulary:

- one stage step = `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`;
- generated closure/effectivity remain explicit optional doctrines:
  `LogOS/LT/Sup/AbstractGeneratedClosure.agda`,
  `LogOS/LT/Effectivity.agda`;
- semantic cap = `LogOS/LT/Theorems/StableCompletion.agda`.

```agda
module ReificationLedgerViaStages {ℓ : Level}
  (C : ZFCore.SetContext {ℓ})
  (S : AR.StagedPredicateReification C)
  (L : RT.ReifiedZFCFO C (AR.staged→restricted S))
  where

  open RT.ReifiedZFCFO L

  model : _
  model = stackFO
```

Optional: discharge ω/Infinity via ν (CoKleene fixed-point spine)
-----------------------------------------------------------------

The CoKleene variant replaces explicit ω/Infinity laws by explicit
completeness/continuity assumptions for the successor-closure endomorphism.

```agda
module ReificationLedgerCoKleene {ℓ : Level}
  (C : ZFCore.SetContext {ℓ})
  (R : AR.PredicateReification C)
  (L : RT.ReifiedZFCFOCoKleene C R)
  where

  open RT.ReifiedZFCFOCoKleene L

  model : _
  model = stackFO
```

Definable Separation (formula-driven subset formation)
------------------------------------------------------

`SetTheory.Definable` provides wrappers that return the separated set together
with its membership characterisation.

For Separation, the formula is read in context `(z , x , params...)`
(`z` at index 0, base set `x` at index 1).

```agda
module DefinableSeparation {ℓ : Level}
  (C : ZFCore.SetContext {ℓ})
  (R : AR.PredicateReification C)
  (L : RT.ReifiedZFCFO C R)
  where

  open RT.ReifiedZFCFO L

  module Def = ForZFCStackFO stackFO
  open Def using (SetU; _∈_)

  -- Example: "z ∈ param0" (with `param0` at de Bruijn index 2 under Separation).
  P∈param0 : Formula
  P∈param0 = (var zero) ∈F (var (suc (suc zero)))

  module _ (x y : SetU) where
    defaultVal : Def.Valuation
    defaultVal _ = μ Def.EmptyV tt

    ρ : Def.Valuation
    ρ = Def.extend y defaultVal

    sep
      : Σ SetU
          (λ s →
            ∀ z →
              (z ∈ s)
                ↔ ((z ∈ x) × Def.evalFormula P∈param0 (Def.extend z (Def.extend x ρ))))
    sep = Def.separateByFormula P∈param0 ρ x
```

Definable Replacement (formula-driven relational image)
-------------------------------------------------------

For Replacement, the formula is read in context `(u , z , params...)`
(`u` at index 0, image element `z` at index 1).

The first-order Replacement schema is functional, so we also supply a
`FunctionalOnX` witness.

```agda
module DefinableReplacement {ℓ : Level}
  (C : ZFCore.SetContext {ℓ})
  (R : AR.PredicateReification C)
  (L : RT.ReifiedZFCFO C R)
  where

  open RT.ReifiedZFCFO L

  module Def = ForZFCStackFO stackFO
  open Def using (SetU; _∈_)

  -- Example relation: "z ≈ u" (u at 0, z at 1).
  R-id : Formula
  R-id = (var (suc zero)) ≈F (var zero)

  module _ (x : SetU) where
    defaultVal : Def.Valuation
    defaultVal _ = μ Def.EmptyV tt

    fun : Def.FunctionalOnX R-id defaultVal x
    fun u u∈x =
      u
        , ( Def.refl≈ u
          , (λ z′ hz′ → hz′)
          )

    img
      : Σ SetU
          (λ s →
            ∀ z →
              (z ∈ s)
                ↔ (Σ SetU (λ u → u ∈ x × Def.evalFormula R-id (Def.extend u (Def.extend z defaultVal)))))
    img = Def.imageByFormula R-id defaultVal x fun
```

Proof closure + quotation (kernel-native)
-----------------------------------------

For the kernel-native proof/closure story (provability as a `GuardedClosure` on theories, `closeTheory`,
and the induced quotation port), see:

- `docs/Interpretations/Applications/HowTo_Use_Deductive_Closure.lagda.md`
