<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# MetaTheory — A 2-Cell Basis (Thin Shadow Factorisation and Boundary Semantics)

This note lists the mechanised components used by the architecture.

Mechanised module: `LogOS.Apps.LogicArchitecture.MetaTheory.Basis`.

```agda
{-# OPTIONS --safe #-}
module docs.Core.MetaTheory.Basis where

open import LogOS.API.LT
```

## What Is Mechanised (and where)

The module `LogOS.Apps.LogicArchitecture.MetaTheory.Basis` is a **navigation module**.
The mechanised development is split into coherent components:

- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps`:
  - minimal **2-cell calculus interface** `TwoCellOps` (objects, 1-cells, 2-cells, vertical composition, whiskering),
  - **thinification** `thinify₂ : TwoCellOps … → Thin2Cat …`,
  - law packages `TwoCellOpsLaws` and `thinify₂-laws : TwoCellOpsLaws C → Thin2CatLaws (thinify₂ C)`.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat`:
  - “maximal 2D claim” interfaces for **strict 2-categories**, both:
    - horizontal composition as primitive (`Strict2CatH`), and
    - whiskering + middle-four interchange as primitive (`Strict2CatW`),
  - basis translation `Strict2CatH→W` and forgetful projections to `TwoCellOps`/`Thin2Cat`.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow`:
  - the **Central Theorem of Logic Architecture** (thin shadow factorisation):
    - `RefinementShadow C` = a chosen refinement relation on 1-cells, stable under whiskering, and sound for 2-cells,
    - `shadowThin2Cat : RefinementShadow C → Thin2Cat …`,
    - canonical shadow `canonicalShadow : TwoCellOps … → RefinementShadow …`,
    - `canonicalShadow≡thinify₂ : shadowThin2Cat (canonicalShadow C) ≡ thinify₂ C`.
  - approximation as a canonical factor map:
    - `shadowApprox : Thin2Functor (thinify₂ C) (shadowThin2Cat S)`.
  - inclusion of shadows induces canonical thin 2-functors:
    - `shadowWeaken : Shadow≤ S T → Thin2Functor (shadowThin2Cat S) (shadowThin2Cat T)`.
  - approximation measures:
    - `Shadow≤` = inclusion of refinement relations (a preorder of approximations).
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView`:
  - `ShadowByView` + `shadowFromView` = shadows induced by explicit boundary semantics (`View`) on each hom,
    dependent-first: the boundary preorder may vary by object pair `O A B`,
  - `pairShadowByView` + accounting lemmas: “adding probes makes approximation finer”.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowInitiality`:
  - contextual shadow initiality/forcedness: `ShadowForcedByView`.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core`:
  - whiskering-stable homwise presentations over a fixed boundary semantics:
    - `BoundaryPresentation`,
    - `CompleteBoundaryPresentation`,
    - `BoundaryKernelAt`,
    - `BoundaryHomPreorder`,
    - `BoundaryPresentationWorld`,
  - canonical thin approximation of bicategory-shaped presentations into the boundary world:
    - `BoundaryWorld`,
    - `bicategoryBoundaryReflection`,
    - `canonicalShadow≤boundaryShadow`,
  - homwise LT internalisation of that boundary world:
    - `boundaryHomPreorder-isCodePreorder`,
    - `completePresentation↔boundaryKernelCanonical`,
  - equivalence of complete presentations over the same `ShadowByView`:
    - `CompleteBoundaryPresentationsEquivalent`,
    - `completeBoundaryPresentationsEquivalentBundle`,
    - `CompleteBoundaryPresentationPackage`,
    - `completeBoundaryPresentationFiber`,
    - `completeBoundaryPresentationNoFork`.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic`:
  - the native internal capstone object
    `MechanisableLogicWorld`,
  - canonical witness `mechanisableLogicWorld`,
  - stable theorem-facing aliases
    `MechanisableBoundarySemanticsTheorem` /
    `mechanisableBoundarySemanticsTheorem`,
  - one packaged reading of LogOS as a foundational refinement logic of
    mechanisable boundary semantics and explicit collapse.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext`:
  - “context = observables” algebra: weakening order + join (`⊔Ctx`) at 1D and 2D,
  - canonical `IndexedConPreorder` construction from context-indexed views,
  - canonical “forget observables” 2-functors between thin approximations (`forgetThin`),
  - join/meet correspondence: context join induces the shadow meet/GLB (`shadowAt-⊔Ctx₂-glb`).
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.RunningBoundaryGauge`:
  - an EFT/RG-style “running center” boundary gauge with matching coherence,
  - canonical pointwise contractible fibers/no-fork theorems at each context,
  - deliberately not phrased as one indexed centered fiber, because the center
    itself varies with context.
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.UniversalProperties`:
  - small universal-property characterisations:
    - `shadowApprox-asWeaken` (approximation = weakening from the canonical shadow),
    - `shadowWeaken-refl` (weakening by identity = identity functor),
    - `canonical≤` (canonical shadow ≤ any sound shadow).
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory`:
  - bicategory-shaped presentations as additional law bundles over the existing basis (`TwoCellOps` + `TwoCellOpsLaws`),
  - optional strict coherence bundle `BicatWCoherence` in `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory.Strictification` (pentagon + triangle),
  - forgetful projection to `TwoCellOps`/`Thin2Cat` (thinification).
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.PseudoFunctor`:
  - pseudofunctor-shaped presentations over the existing basis (`TwoCellOpsFunctor`),
  - canonical induced `Thin2Functor` between thinifications.

## How This Strengthens Coherence and Consistency (design summary)

LogOS has three orthogonal “knobs” that strengthen the story without hiding assumptions:

1. **Canonical approximation (consistency by forcedness)**:
   induce shadows from explicit observations (`View` / probe suites), and use
   `LogOS.LT.Presentation.ObservationInitiality` to get minimality/forcedness.

2. **2D coherence (coherence by law bundles)**:
   keep operations (`TwoCellOps`) and laws (`TwoCellOpsLaws`, strict 2-cat law records) separate,
   and state any additional interchange/functoriality/coherence you need as explicit fields.

3. **Guarded self-reflection (consistency by modality)**:
   any Lawvere-style reflection in LogOS is formulated on the thin shadow hom-preorders via
   `GuardedClosure` / `KZModality` (`LogOS.LT.Flow`, `LogOS.LT.AbstractKZ`), not as an implicit meta-principle.

## Boundary semantics reflection (mechanised consequence)

For a bicategory-shaped presentation `B : BicatW ...` and a fixed boundary semantics
`S : ShadowByView (BicatW→TwoCellOps B) O`, the module
`LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core` packages:

- the canonical thin approximation
  `bicategoryBoundaryReflection : Thin2Functor (BicatW→Thin2Cat B) (BoundaryWorld S)`,
- the boundary-forced comparison
  `canonicalShadow≤boundaryShadow`,
- and the fact that any two complete homwise presentations over the same `S`
  induce equivalent presentation worlds via
  `BoundaryPresentationWorld`,
  `CompleteBoundaryPresentationsEquivalent`,
  `completeBoundaryPresentationsEquivalentBundle`.

This is the precise metatheoretic bridge from higher 2-cell presentations to the
LT-style thin boundary world: the boundary semantics fixes the shadow, and
complete presentations only change the derivation interface inside that fixed
shadow. More sharply, each hom of that boundary world is already an LT kernel
`BoundaryKernelAt S {A} {B} = kernelFromView (μ S {A} {B})`, and the reflected
hom preorder is definitionally its canonical code preorder by
`boundaryHomPreorder-isCodePreorder`.

## Foundational logic package

The stronger composite Apps-side theorem is packaged in
`LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic`.

For fixed bicategory-shaped source logic `B` and fixed boundary semantics
`S : ShadowByView (BicatW→TwoCellOps B) O`, the bundle
`MechanisableLogicWorld B O S` now internalises the capstone theorem directly.
Its explicit fields package:

- the canonical thin boundary world and reflection into it,
- complete-presentation invariance over that fixed boundary semantics,
- the centered fibre of complete presentations over that same fixed boundary
  semantics, so local presentation independence is available as a first-class
  contractible-fibre/no-fork object,
- homwise LT internalisation of that boundary world by canonical kernels and
  their code preorders,
- a native guarded self-reference fibre on each reflected hom, exposing
  KZ-style partial reflection, stable completion into quote kernels, and the
  guarded Lawvere fixed-point/obstruction principles,
- the LT-core architectural normal form data,
- and the fibrewise extensional reflector inside each classical-limit fibre.

The older theorem-facing aliases
`MechanisableBoundarySemanticsTheorem` /
`mechanisableBoundarySemanticsTheorem`
are retained as stable views of this native object.

This remains the seed capstone object for the metatheory. The apps-side summit
capstone surface in `LogOS/Apps/Summit/**` does not replace it: the summit packages
recognition by conservative generalisation, quantitative capstones, and the
guarded obstruction over a chosen recognised fragment on top of this seed.

So the strongest careful reading currently supported by the repository is:

- richer bicategory-shaped presentations canonically thin-reflect into an
  explicit boundary world,
- each hom of that world is canonically an LT kernel, and complete
  presentations over the same boundary are equivalent interfaces to that
  kernel’s canonical preorder,
- guarded evaluator reflection and the Lawvere-style mirror are internal
  projections of that same world rather than external add-ons,
- and extensional logic appears fibrewise as explicit reflective collapse under
  classical-limit evidence.

The summit layer simply collects those consequences in a downstream-facing
apps-side form once a downstream logic is equipped with the strong
mechanisable adjective built from conservative generalisation plus compatible
quantitative and quoted/self-reference structure. An optional further doctrine,
`ObservationalSufficiency` in `LogOS/Apps/Summit/Admissibility.agda`, states
when extra visible downstream refinement is image-local and ambiently sound,
so that conservativity yields a no-backflow theorem on the recognised image.
