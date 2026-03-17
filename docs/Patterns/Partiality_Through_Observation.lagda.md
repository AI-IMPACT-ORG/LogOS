<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: partiality through observation

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Partiality_Through_Observation where

open import LogOS.API.LT

import LogOS.Apps.TuringCategory.PartialMaps as PM
open import LogOS.Apps.TuringCategory.Lift using (LiftCP)
import LogOS.Apps.TuringCategory.Bridge.KernelToPar as K2Par

-- The two bridge constructors (named here so the types show up in this doc).

totalOnCode
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K K' : Kernel ℓ ℓRel ℓCode}
  → KernelHom K K'
  → PM.PartialMap (CodePreorder K) (CodePreorder K')
totalOnCode = K2Par.kernelHomToPartialMap

observedOnCode
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (V : View (Con (bnd K')) (LiftCP O))
  → (monoV : MonoMap (bnd K') (LiftCP O) (μ V))
  → KernelHom K K'
  → PM.PartialMap (CodePreorder K) O
observedOnCode = K2Par.kernelHomToObservedPartialMap

BoundaryObservationPort
  : ∀ {ℓ ℓRel ℓCode ℓObs : Level}
  → Kernel ℓ ℓRel ℓCode
  → ConPreorder ℓObs ℓRel
  → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓObs))
BoundaryObservationPort = K2Par.BoundaryObservationPort

observedByPort
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → BoundaryObservationPort K' O
  → KernelHom K K'
  → PM.PartialMap (CodePreorder K) O
observedByPort = K2Par.observedPartialMap

canonicalObserved
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {O : ConPreorder ℓCode ℓRel}
  → (Pₒ : BoundaryObservationPort K' O)
  → (h : KernelHom K K')
  → Presentation (K2Par.observedCodeView Pₒ h)
canonicalObserved = K2Par.canonicalObservedPresentation
```

This note records a LogOS design stance that matters for the “Turing category / partial maps” story:

> **Kernel morphisms are not where partiality lives.**
> If you want *genuine* partiality (`none`), it must enter through an **explicit observation** (`View`) into a
> lifted interface (`LiftCP`).

The point is to keep “meaning changes” auditable and compositional, in the same spirit as
`docs/Patterns/Meaning_Injection_Compartments.lagda.md`.

## What is a “partial map” here?

The pack `LogOS/Apps/TuringCategory/PartialMaps.agda` defines a canonical “classical” partial-map model `Par`:

- objects: `ConPreorder`,
- morphisms `X ⇀ Y`: monotone functions `Con X → Con (LiftCP Y)`,
- composition: Kleisli composition via `bindᴸ`.

The lift `LiftCP` is the minimal bottom-adjunction:

- values are `none` or `some y`,
- refinement extends the base preorder with `none ≼ _` (equivalently `none ⊑ _`; bottom refines into everything).

Code anchor: `LogOS/Apps/TuringCategory/Lift.agda`.

## The design choice (where `none` is allowed to appear)

In the LT spine, a kernel already *is* an observation choice:

- a boundary preorder `bnd(K)`,
- a code type `Code(K)`,
- a decoder `decode : Code(K) → Con (bnd(K))`.

Crucially, **kernel morphisms** (`KernelHom`) are designed as *meaning-preserving adapters*: they carry refinement-first
decode coherence (`≈`), and are compared in `LOG` by refinement of decoded behaviour (with strictness available only as an explicit opt-in check).

So when we map kernel morphisms into the partial-map model `Par`, the structural reading is:

- treat every `KernelHom` as a **total** partial map on code by wrapping its action in `some`.

This is exactly `totalOnCode` above, and the functor `codeToPar : LOG → Par` in
`LogOS/Apps/TuringCategory/Bridge/KernelToPar.agda`.

If you want maps that can return `none`, LogOS insists that the reason must be explicit:

- you chose an observation `V : View (Con (bnd K)) (LiftCP O)` into a *lifted* interface,
- and the observation itself can be undefined (`μ V _ = none`).

That choice produces a partial map on code by post-composition:

```text
Code(K)  --decode-->  Con(bnd(K))  --μ V-->  Con(LiftCP O)
```

This is `observeOnCode` in `LogOS/Apps/TuringCategory/Bridge/KernelToPar.agda`.

To keep that choice auditable, the bridge now packages the observation as an explicit
`BoundaryObservationPort`. This retains the boundary-facing `View`, its monotonicity
witness, and the induced code-facing `View` used for presentation theorems.

For a morphism `h : KernelHom K K'`, observation-induced partiality is the same idea on the output boundary:

```text
Code(K)  --mapCode h-->  Code(K')  --decode-->  Con(bnd(K'))  --μ V-->  Con(LiftCP O)
```

This is `observedOnCode` above.

The port form `observedByPort` is the same construction with the observation packaged
once and reused across the bridge and observation-program layer. This avoids keeping a
second Turing-specific “gate” representation in parallel with the bridge itself.

The same port also determines a canonical observed-code presentation `canonicalObserved`.
More strongly, for fixed observation data the bridge now packages complete
observed presentations as a centered fibre:

- `K2Par.canonicalCompleteObservedPresentationPackage`
- `K2Par.completeObservedPresentationFiber`
- `K2Par.completeObservedPresentationNoFork`

So complete observed presentations do not merely “agree”; they contract to the
canonical extensional partial semantics induced by that fixed port and kernel
morphism. The older theorem names are now corollaries or boundary-facing
readings of that centered statement:

- `K2Par.observedPartialityCanonicality`
- `K2Par.observedFullAbstraction`
- `K2Par.observedEquivFullAbstraction`
- `K2Par.observedPresentation↔partialMap`

The bridge also transports kernel-hom refinement into pointwise refinement of
the observed partial maps by `K2Par.observedPartialMapTransport`. So
extensionality-through-observation is now factored through the generic LT
presentation-independence and centering story rather than a pack-local
equivalence argument.

## Why this is LogOS-aligned

- **No silent semantics drift:** total kernel adapters stay total; partiality only comes from a declared observation
  gate.
- **Boundary-first honesty:** “undefined” is a statement about what the observer can extract from the boundary, not a
  mysterious behaviour hidden in the kernel morphism.
- **Compositionality in the target:** once you are in `Par`, partiality composes by Kleisli bind; if you want the
  observation choices to remain inspectable, you can further decorate/Σ-totalise (e.g.
  `LogOS/Apps/TuringCategory/Bridge/ObservationPrograms.agda`). That layer is now deliberately
  thin: its “gates” are just the explicit boundary observation ports from `KernelToPar`, and the
  constructors accept that port form directly (`runThenObservePort`), so the inspectable layer
  reuses the same observation packaging instead of defining a second one.

## Navigation pointers

- Bridge code (structural + observation-induced): `LogOS/Apps/TuringCategory/Bridge/KernelToPar.agda`
- CH(2008) Turing-category pack (CT-shaped): `LogOS/Apps/TuringCategory/CH2008.agda`
- CT vs CTD navigation: `LogOS/Apps/TuringCategory/CTandCTD.agda`
- Deutsch-style category (port stack): `LogOS/Ports/AbstractDeutsch2Cat.agda`
- CTD universality (weak terminality in the flow port category `LogOS.LT.LOG.Flow2Cat.WithPort`, separate story): `LogOS/Ports/Universality/CTD/Ledger.agda`
