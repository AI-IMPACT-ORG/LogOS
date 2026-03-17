<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Summit

```agda
{-# OPTIONS --safe #-}
module docs.Results.Summit where

import LogOS.API.LT
```

This page is an apps-side capstone note. It does not add a new theorem layer.
Instead it collects consequences of theorem spines that already exist lower in
the repository.

Recognition by conservative generalisation
------------------------------------------

The summit recognises a downstream logic as mechanisable when it contains a
conservatively generalised image of a seed mechanisable boundary world.

Code anchors

- `LogOS/Apps/Summit/Policy.agda`
- `LogOS/Apps/Summit/Recognition.agda`
- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`
- `LogOS/LT/Thin2Functor.agda`

Mechanisable downstream adjective
---------------------------------

The summit now treats the extra quantitative and quoted/self-reference choices
as part of the strong apps-side adjective “mechanisable” for a downstream
logic. In other words, the summit does not start from three unrelated external
policies. It starts from one downstream mechanisable package, and then the
recognised fragment, the quantitative capstones, and the diagonal obstruction
follow as collected consequences.

The bare conservative-generalisation witness still exists, but it is now only a
constructor into that stronger adjective. This is the honest stopping point of
the current mathematics: the codebase shows strong forcing on the recognised
mechanisable image, but it does not yet derive the quantitative doctrine or the
quoted/self-reference data from conservativity alone.

Code anchors

- `LogOS/Apps/Summit/Theorem.agda`
- `LogOS/Apps/Summit/Mechanisable.agda`
- `LogOS/Apps/Summit/Policy.agda`
- `LogOS/Apps/Summit/Recognition.agda`
- `LogOS/Apps/Summit/Admissibility.agda`
- `LogOS/Apps/Summit/Quantitative.agda`
- `LogOS/Apps/Summit/Obstruction.agda`
- `LogOS/Apps/Summit/Mechanisable.agda`

Optional observational-sufficiency doctrine
-------------------------------------------

The summit now isolates one optional metalogical guardrail, with the formal
name `ObservationalSufficiency` and the informal nickname “No Ghost In The
Machine”.

It is not the tautological slogan “whatever does not matter does not matter”.
Instead it is a small admissibility discipline on an extra downstream visible
refinement judgement over the recognised mechanisable image:

- the judgement is stated on visible downstream morphisms,
- it is invariant under visible downstream equivalence,
- and it is sound for the ambient downstream refinement relation.

Only after those guardrails are fixed does conservativity of the recognised
fragment yield the nontrivial conclusion: any visible downstream collapse
already collapses in the seed-visible image.

Code anchors

- `LogOS/Apps/Summit/Admissibility.agda`
- `LogOS/Apps/Summit/Mechanisable.agda`
- `LogOS/LT/Thin2Functor.agda`
- `LogOS/Apps/Summit/Recognition.agda`

Local shared-boundary symmetry
------------------------------

The summit now exposes the sharper local result that was already latent in the
codebase: once a recognised mechanisable image is fixed, complete
presentations over that same shared boundary form a centered fibre. The
canonical complete presentation is the center, and any admissible visible
collapse on the image descends uniformly through that center.

This is the precise point where the repository upgrades the literature-style
presentation-independence story. It is not merely “complete presentations agree
for one fixed view”. It is “two systems over one fixed shared boundary can be
compared locally, without globally collapsing the rest of the downstream
logic”.

The summit now sharpens this one step further. A symmetry-respecting summit
package is now understood over one recognised image and one fixed mechanisable
payload: quantitative cut data plus the quoted/self-reference obstruction
policy are held fixed, and only the shared-boundary complete presentation is
allowed to vary. The comparison relation is therefore intentionally induced by
that common presentation shadow. The canonical summit package is weak-terminal
in this image-visible fibre, and any two such packages agree on their image
shadow by contracting through the same canonical center. This is a local
descent theorem, not a global uniqueness theorem for arbitrary downstream
structure.

Code anchors

- `LogOS/LT/View.agda`
- `LogOS/LT/Presentation/Transport.agda`
- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/ObservationReflection/Core.agda`
- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`
- `LogOS/Apps/Summit/Theorem.agda`

Collected quantitative consequences
-----------------------------------

The summit does not re-derive quantitative results. It packages the already
landed critical-cut, observational-Landauer-bridge, and
least-stable-approximation
surfaces under one apps-side capstone route.

Pedantic packaging note:

- `QuantitativeSummit` is now sharp-cut-primary by construction,
- the critical cut is not stored independently but derived as
  `SharpCut.base sharpCut`,
- this removes the earlier possibility of packaging unrelated critical and
  sharp threshold data into one apparent summit witness.

Code anchors

- `LogOS/Apps/Summit/Quantitative.agda`
- `LogOS/Ports/CriticalParameter.agda`
- `LogOS/Ports/AbstractLandauerObservational.agda`
- `LogOS/Ports/Valuation/AbstractQuanticNucleus.agda`
- `LogOS/Ports/Valuation/AbstractConnesKreimer.agda`

Diagonal obstruction
--------------------

Once a compatible quoted/self-reference policy is chosen on the recognised
mechanisable fragment, the existing guarded Lawvere obstruction is no longer
optional. The summit packages that obstruction apps-side; it does not reprove
it.

Code anchors

- `LogOS/Apps/Summit/Obstruction.agda`
- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`
- `LogOS/Ports/Reification/GuardedLawvere.agda`

What is and is not claimed
--------------------------

Defined here

- a thin policy layer for conservative generalisation and explicit obstruction
  data
- a recognition surface for mechanisable fragments
- an optional summit-side observational-sufficiency doctrine for extra visible
  downstream refinement
- a strong downstream mechanisable adjective packaging the extra summit data
- a quantitative capstone surface over recognised images
- the quantitative capstone is coherence-tight by construction: sharp cut is
  primitive, critical cut is derived
- a diagonal-obstruction surface over an explicitly chosen fragment
- direct consequence functions `mechanisableRecognition`,
  `mechanisableQuantitative`, `mechanisableObstruction`, and
  `mechanisablePayloadOnImage` from the downstream mechanisable adjective
- a constructor `atLeastAsStrongAsMechanisable→mechanisable` from the weaker
  conservative-generalisation entry point
- a local symmetry/descent theorem family over recognised shared boundaries:
  `symmetryRespecting→noForkOnImage` and
  `symmetryRespecting→weakTerminalOnImage`
- a package-level local symmetry/descent theorem family over one recognised
  image:
  `summitPackage→noForkOnImage`,
  `summitPackage→weakTerminalOnImage`, and
  `summitPackages→sameImagePresentation`

Not claimed here

- no theorem that every thin logic is mechanisable
- no reconstruction of a mechanisable world from arbitrary downstream data
- no automatic transport of diagonal obstruction through arbitrary functors
- no claim that observability alone already forces every admissible downstream
  package without an extra metalogical doctrine
- no global uniqueness theorem for arbitrary downstream packages outside the
  recognised/shared-boundary image
- no new equality-first theorem discipline
