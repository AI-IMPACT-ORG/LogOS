<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# MetaTheory — Boundary-Controlled Approximation

```agda
{-# OPTIONS --safe #-}
module docs.Core.MetaTheory.Observation_Controlled_Approximation where

open import LogOS.API.LT
```

Definitions (mechanised)
------------------------

- Boundary contexts: `ObsContext`, `ObsContext₂`.
- Context order: weakening (`_≤Ctx_`, `_≤Ctx₂_`).
- Context joins: `_⊔Ctx_`, `_⊔Ctx₂_`.
- Shadows induced by boundary views: `ShadowByView`.

Core statements (mechanised)
----------------------------

- Context join corresponds to shadow meet/GLB.
- Strengthening contexts adds observables; weakening forgets observables.
- Context-indexed approximation is functorial.
- Boundary-sound bicategory-shaped presentations admit a canonical thin
  reflection into the boundary-induced shadow:
  `bicategoryBoundaryReflection`.
- The canonical thin approximation is exactly weakening from the canonical
  shadow into the boundary-induced one:
  `canonicalShadow≤boundaryShadow` together with
  `bicategoryBoundaryReflection-asWeaken`.
- Complete homwise presentations over the same explicit boundary semantics
  `S : ShadowByView ...` induce equivalent thin shadows:
  `BoundaryPresentationWorld`,
  `CompleteBoundaryPresentationsEquivalent`,
  `completeBoundaryPresentationsEquivalentBundle`.
- The optional opacity pack is the finitary downstream counterpart:
  once a finite observed family is fixed, explicit factorisation and
  finite-loss witnesses quantify how much observational structure is lost.

Boundary semantics theorem
--------------------------

Mechanised module:
`LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core`.

Formal reading:

- fix `B : BicatW ...`,
- fix `S : ShadowByView (BicatW→TwoCellOps B) O`,
- then `bicategoryBoundaryReflection` gives a canonical
  `Thin2Functor (BicatW→Thin2Cat B) (BoundaryWorld S)`.

This is called a “reflection” in the metatheory note only in the weak,
mechanised sense of a canonical thin approximation map. No adjunction claim is
made here.

If `P` and `Q` are complete whiskering-stable homwise presentations over the
same `S`, then `BoundaryPresentationWorld P` and `BoundaryPresentationWorld Q`
are related by a packaged witness
`CompleteBoundaryPresentationsEquivalent P Q ...`. So the boundary semantics
fixes the thin shadow, and complete presentations only supply alternative
derivation interfaces inside it. Homwise, this is already internal to LT: the
reflected boundary hom at `A , B` is canonically the code preorder of
`BoundaryKernelAt S {A} {B}`, and complete presentations are equivalent to that
canonical kernel preorder via `completePresentation↔boundaryKernelCanonical`.

Pointers
--------

- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObsContext`
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView`
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowInitiality`
- `LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core`

Foundational logic corollary
----------------------------

The Apps-side bundle
`LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic`
packages the stronger composite claim:

- boundary-sound bicategory-shaped logic canonically thin-reflects into a
  `BoundaryWorld`,
- each reflected hom is canonically an LT kernel and every complete boundary
  presentation is an equivalent interface to its canonical code preorder,
- each reflected hom also carries an internal guarded self-reference fibre
  `BoundarySelfReferenceFibre`, with KZ-style `quot`/`evalm`, stable completion,
  and the guarded Lawvere fixed-point/obstruction schema,
- and inside each explicit classical-limit fibre, displayed boundary-first
  logic reflectively strictifies by
  `fiberwiseExtensionalReflection`.

This is the precise sense in which LogOS supports a “foundational logic”
reading. The claim is not that every logic has a global free collapse. The
claim is that explicit boundary semantics fixes a canonical thin refinement
world, that world is already homwise internal to LT by canonical kernels, and
its guarded self-reference discipline is internal there by construction;
extensionality is recovered only by explicit typed strictification.
