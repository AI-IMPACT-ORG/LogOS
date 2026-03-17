<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Refinement-first results

```agda
{-# OPTIONS --safe #-}
module docs.Results.Refinement_First_Results where

import LogOS.API.LT
```

This page is the shortest route to the repository's load-bearing results if you
want the theorem spine before the interpretations.

Result family 1: observation forces refinement
----------------------------------------------

Once a `View` or probe suite is fixed, the coarsest admissible refinement that
respects that observation is forced. This is the base discipline that keeps the
rest of the architecture honest.

Code anchors

- `LogOS/LT/Presentation/ObservationInitiality.agda`
- `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`
- `LogOS/LT/Theorems/DependentProbeSuiteRepresentation.agda`
- `LogOS/LT/Presentation/ExtensionalMinimality.agda`

Result family 2: translation commutes with normalisation up to refinement
-------------------------------------------------------------------------

Effectivisation, stable completion, and evaluator reflection are phrased as
transport laws up to `⊑` or `≈`, not as ambient equality theorems. The same
cluster now also carries the reflective-image reading explicitly: Galois-induced
closures identify stable points with the right image up to refinement witness,
and stable completion is the canonical quotation target rather than merely one
possible factoring.

Code anchors

- `LogOS/LT/Theorems/Effectivisation.agda`
- `LogOS/LT/Theorems/StableCompletion.agda`
- `LogOS/LT/Theorems/EvaluatorReflection.agda`

Result family 3: architecture admits displayed normal forms
-----------------------------------------------------------

The repository's port architecture already has a typed theorem surface:
displayed/totalised normal forms with refinement inherited from the base.

Code anchors

- `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`
- `LogOS/LT/LOG/Discipline/PortsAsDisplayed.agda`
- `LogOS/LT/DisplayedThin2Cat.agda`
- `docs/Patterns/Ports_As_Displayed.lagda.md`

Result family 4: completion, packets, and Galois transport
----------------------------------------------------------

Closure, packets, and Galois-style completion are all exposed as explicit
result families over the same refinement-first base. In particular,
`AbstractGaloisConnection` now exposes the stable/right-image correspondence as
the generic source of “effective semantics lives in the reflective image”.

Code anchors

- `LogOS/LT/Theorems/AbstractGaloisConnection.agda`
- `LogOS/LT/Theorems/EffectivePackets.agda`
- `LogOS/LT/Theorems/PacketCorollaries.agda`
- `LogOS/LT/Effectivity.agda`

Result family 5: quantitative cutpoints and conditional lower bounds
--------------------------------------------------------------------

The quantitative doctrine now has one canonical cut vocabulary and one
canonical loss vocabulary. Exact opacity/visibility thresholds package into
`CriticalCut`/`SharpCut`, and finite count-loss feeds an explicit observational
Landauer bridge, with unit-loss exposed only as a corollary.

Code anchors

- `LogOS/Ports/CriticalParameter.agda`
- `LogOS/Ports/Opacity/Profile.agda`
- `LogOS/Ports/Opacity/FiniteCompression.agda`
- `LogOS/Ports/AbstractLandauerObservational.agda`

Result family 6: approximation and centering surfaces
-----------------------------------------------------

The context-approximation and centering-based quotation surfaces are already
organised as result families, not as downstream metaphors.

Code anchors

- `LogOS/LT/Theorems/ContextApproximation.agda`
- `LogOS/LT/Theorems/BoundaryGauge.agda`
- `LogOS/LT/Theorems/Centering.agda`
- `LogOS/LT/Theorems/CenteringQuote.agda`

Result family 7: summit capstone over mechanisable fragments
------------------------------------------------------------

The repository now has an apps-side summit capstone route that sits above the
existing capstone theorem spines without replacing them. Its role is to say:
once a downstream logic carries a conservatively recognised mechanisable
fragment, the reflective-image, presentation-invariance, quantitative-cut, and
guarded-obstruction stories can be read as one coherent apps-side result
surface. The current capstone theorem surface phrases that as a two-step story:
`atLeastAsStrongAsMechanisable→mechanisable` constructs the strong downstream
mechanisable adjective, and the direct consequence functions
`mechanisableRecognition`, `mechanisableQuantitative`,
`mechanisableObstruction`, and `mechanisablePayloadOnImage` expose what that
adjective already fixes. The summit now also isolates one optional
metalogical guardrail, `ObservationalSufficiency`, saying that any extra
visible downstream refinement judgement must be invariant under visible
equivalence and sound for ambient downstream refinement; conservativity then
gives a no-backflow theorem on the recognised image. The newest sharpening is a
local shared-boundary symmetry theorem: complete presentations over a fixed
recognised boundary contract to the canonical center, so symmetry-respecting
visible collapse cannot create a semantic fork on that image. The latest
package-level refinement is that whole symmetry-respecting summit packages over
one recognised image and one fixed mechanisable payload are compared by their
shared-boundary presentation shadow, so the canonical package is weak-terminal
in that image-visible fibre and any two such packages agree on the same image
presentation.

Code anchors

- `LogOS/Apps/Summit/Policy.agda`
- `LogOS/Apps/Summit/Recognition.agda`
- `LogOS/Apps/Summit/Mechanisable.agda`
- `LogOS/Apps/Summit/Admissibility.agda`
- `LogOS/Apps/Summit/Quantitative.agda`
- `LogOS/Apps/Summit/Obstruction.agda`
- `LogOS/Apps/Summit/Theorem.agda`
- `docs/Results/Summit.lagda.md`

Suggested reading order
-----------------------

1. `ObservationInitiality`
2. `ProbeSuiteRepresentation` / `DependentProbeSuiteRepresentation`
3. `Effectivisation`
4. `StableCompletion`
5. `CriticalParameter` / `Profile`
6. `ArchitecturalNormalForm`
7. One of `AbstractGaloisConnection` or `ContextApproximation`, depending on
   whether you want closure/completion or approximation geometry next.
8. `docs/Results/Summit.lagda.md` once you want the apps-side capstone view.

Catalog entrypoints
-------------------

- `LogOS/API/Theorems/Core.agda` — the small, load-bearing theorem surface.
- `LogOS/API/Theorems/Strictification.agda` — the explicit strictification theorem surface.

What is not claimed
-------------------

- no ambient equality-first extensionality discipline; most results live at the
  `⊑`/`≈` level;
- no global completeness theorem outside explicit pack-local hypotheses;
- no collapse of optional doctrines into kernel primitives.
