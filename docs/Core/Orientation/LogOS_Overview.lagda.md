<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS — Overview (v1.1)

This document is the landing page for the 1.1 Agda library: what LogOS is, how it is organised, and where to
go next.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Orientation.LogOS_Overview where

-- Sync guard: public docs should prefer the curated API surface.
import LogOS.API.LT
```

<a id="orientation"></a>
Orientation (start here)
------------------------

Canonical route:

- Docs hub: `docs/README.md`
- Core docs hub: `docs/Core/README.md`
- Design-target spec (typechecked, code-linked): `docs/Core/Spec/LogicalTransformers.lagda.md`
- Repo-aligned spec (guardrails + claims): `docs/Core/Spec/LogOS_Specification.lagda.md`
- Refinement-first result spine: `docs/Results/Refinement_First_Results.lagda.md`
- Audit guide (how to verify claims): `docs/Core/Orientation/Audit_Guide.lagda.md`
- High-risk conventions (fast boundary warnings): `docs/Core/Orientation/High_Risk_Conventions.lagda.md`
- Architecture (layering that CI enforces): `docs/Core/Architecture/Diagram.lagda.md`
- Architecture view (tetrahedron reading): `docs/Core/Architecture/Tetrahedron.lagda.md`
- Derived construction/discipline face: `docs/Core/Architecture/BiPyramid.lagda.md`

Optional reader routes:

- Interpretations hub (audience paths + pack readings): `docs/Interpretations/README.md`
- ZF/ZFC quickstart: `docs/Interpretations/Orientation/ZFC_Quickstart.lagda.md`

Paths (choose one):

- Mathematics: `docs/Interpretations/Paths/Mathematics.lagda.md`
- Physics: `docs/Interpretations/Paths/Physics.lagda.md`
- Programming language theory: `docs/Interpretations/Paths/PLT.lagda.md`
- Systems / architecture: `docs/Interpretations/Paths/Systems.lagda.md`
- Contributors: `docs/Interpretations/Paths/Contributing.lagda.md`

Reference (lookup):

- Mechanisation map (implemented vs planned): `docs/Core/Spec/Implementation_Map.lagda.md`
- Refinement-first result spine: `docs/Results/Refinement_First_Results.lagda.md`
- Design notes index: `docs/Patterns/All.lagda.md`
- Views index (one kernel, many readings): `docs/Interpretations/Views/All.lagda.md`
- Glossary + ontology: `docs/Core/Orientation/Ontology.lagda.md`
- Weak vs strict `KernelHom`: `docs/Patterns/Clarifications/Weak_vs_Strict_KernelHom.lagda.md`
- Docs index (generated): `docs/Generated/Docs_Index.md`
- Policy index (generated): `docs/Generated/Policy_Index.md`
- Module index (generated): `docs/Generated/Module_Index.md`
- Layer order legend (generated): `docs/Generated/Architecture_Layer_Order.md`

Full inventory (generated): `docs/Generated/Docs_Index.md`

Project goals: `docs/Core/Project/Design_Goals.md`

Go straight to code:

- Curated API surface: `LogOS/API/LT.agda`
- Kernel definition: `LogOS/LT/Kernel.agda`

<a id="conceptual-spine"></a>
Conceptual spine (self-similar presentation)
--------------------------------------------

The documentation and code share a single, self-similar construction path:

- `ConPreorder`: boundary truth/refinement carrier (`LogOS/LT/ConPreorder.agda`)
- `View`: presentation discipline via pullback (`LogOS/LT/View.agda`)
- `Kernel`: boundary + code + decode (`LogOS/LT/Kernel.agda`)
- `BoundaryHom`: boundary transport (G-tier; H-tier guards are encoded as boundary constraints)
  (`LogOS/LT/BoundaryHom.agda`)
- `KernelHom`: adapters as boundary transport + displayed realisers, with refinement-first decode coherence (`≈`)
  (`LogOS/LT/Hom.agda`; equality is quarantined to explicit `Strictification` / `Definitional` lanes, with strict kernel morphisms exposed only via `LogOS.API.Strictification`)
- Coherence coercions (explicit “subtyping” between strict/≈/under modes): `LogOS/LT/Hom/Coercions.agda`
- `LOG`: thin 2-category with boundary-driven observational refinement (`_⇒∂_` in base `LOG`; realiser-first `_⇒_` is equivalent)
  (`LogOS/LT/LOG/Kernel2Cat.agda`)
- `LOGᴳ` / `LOGᴳʳ`: boundary-only base 2-category and its displayed realiser totalisation
  (boundary-only base vs displayed realiser split; weakening functor `toLOG` recovers the usual `LOG` refinement)
  (`LogOS/LT/LOG/Boundary2Cat.agda`, `LogOS/LT/LOG/Implementation2Cat.agda`)
- Exemplar port stack over `LOGᴳ`: `LOGᴳʳ∂` (realisers + contracts; weakening functor back to the contract port category
  `LogOS.LT.LOG.Contract2Cat.WithPort`)
  (`LogOS/LT/LOG/ImplementationContract2Cat.agda`, `LogOS/LT/LOG/Contract2Cat.agda`)
- `DisplayedThin2Cat`: ports as displayed structure over a chosen base thin 2-category (`LogOS/LT/DisplayedThin2Cat.agda`)
- `DecoratedThin2Cat`: decorated categories + forgetful functors (`LogOS/LT/DisplayedThin2Cat.agda`)
- `PortSig`: tagged displayed layers (`LogOS/LT/Ports/PortSig.agda`)
- `PortStack`: typed port stacks (product-stacking, capability projections, substack forgetting) (`LogOS/LT/Ports/PortStack.agda`)
  (internally folds to right-associated `ProductDisplayed` (`LogOS/LT/DisplayedThin2Cat.agda`))
- Law-ports: extra laws with explicit forgetful projections (e.g., `QuotePort`)

Tetrahedron reading (equator + three extension directions)
----------------------------------------------------------

There is a simple *typed architecture view* that matches the mechanised spine:

- one preserved observational **equator** (`LOG`), and
- three common directions of extension:
  - **construction** (stacks/programs/presentations), and
  - **discipline** (displayed layers/ports/contracts/flow/quote, totalised by Σ),
  - **realisation** (one shared boundary, many realisation families).

The key refinement-first stance is that “faces commute” **by local refinement**
(`⊑` / `≈`) rather than by strict equality (`≡`) by default; strictness is an
explicit opt-in check or reflective collapse.

This primary view is documented in:

- `docs/Core/Architecture/Tetrahedron.lagda.md`

and is also packaged as typed structure (no new axioms) on the curated API
surface:

- `LogOS/API/Architecture.agda`

The older bi-pyramid reading remains as the derived construction/discipline
face of the same package:

- `docs/Core/Architecture/BiPyramid.lagda.md`

The generic physics-facing pattern is now explicitly the realisation apex over a
fixed shared distributed-semantics ledger:

- `LogOS/Ports/Realisations/DependentStack.agda`
- `LogOS/Ports/Realisations/Architecture.agda`

One downstream design target is the **Deutsch-style category**: a port stack
over that same ledger (locality + causality + local reversibility). Local
reversibility is implemented as pointwise order-isomorphisms and is
intentionally weaker than unitarity; local unitarity is planned as a
refinement.

The current canonical Deutsch-style implementation is the dependent-locality
(`DependentLocalSemantics`, ultralocal-first) case:

- `LogOS/Ports/AbstractDeutsch2Cat.agda` (parameterised by `DependentLocalSemantics`)

The uniform case is recovered as a special case by choosing constant families of observables and doctrine.

Reading order pointer:

- `LogOS/LT/Index.agda` (contributor-facing index for the LT spine and port infrastructure).

<a id="information-simplification"></a>
Information simplification
--------------------------

- `View` defines observation.
- Pullback along the view defines refinement.
- The coarsest compatible refinement is forced.

Metatheoretic consequence
-------------------------

The LogicArchitecture metatheory now proves a careful higher-dimensional
boundary-semantics statement:

- richer bicategory-shaped presentations canonically thin-reflect into the same
  explicit boundary world,
- and any two complete presentations over the same explicit boundary semantics
  induce equivalent thin shadows.

The newer composite Apps-side theorem pushes that further:

- each hom of the boundary world supplied by that reflection is canonically an
  LT kernel, and complete presentations over the same boundary semantics are
  equivalent interfaces to that kernel’s canonical preorder,
- guarded evaluator reflection and the Lawvere-style fixed-point mirror are
  internal projections of that same boundary-world object,
- and inside each explicit classical-limit fibre, boundary-first displayed
  logic reflectively strictifies to extensional logic.

So the LT discipline is not merely one encoding choice. It is the
canonical thin boundary world forced by explicit boundary semantics, with
different complete presentations changing only the derivation interface inside
that world, and with extensional collapse appearing only as explicit added
structure.

If you want to build a new application pack (contributor route):

- Contributor guide: `docs/Patterns/HowTo/HowTo_Add_App.lagda.md`
- AI/agent instructions (how to not break invariants): [AGENTS.md](../../../AGENTS.md)

What “host-minimal” means (design constraint)
---------------------------------------------

<!-- CLAIM-STAMP: DERIVED | anchor=scripts/check/host_import_check.sh#host-import-check -->

The library is meant to be usable as a small, **stdlib-independent** Agda kernel:

- The build is pinned to `--no-libraries --safe` (see [Makefile](../../../Makefile)).
- Only `LogOS/Host/**` may touch `Agda.Primitive` and `Agda.Builtin.*` (enforced by
  `scripts/check/host_import_check.sh` / `scripts/check/host_surface_check.sh`).
- Everything else imports a curated prelude (`LogOS/Prelude.agda`) and stays within the “safe surface”.

Architecture (hexagonal in code shape)
--------------------------------------

<!-- CLAIM-STAMP: DEFINITION | anchor=docs/Core/Architecture/Diagram.lagda.md#architecture-intended -->

The repository layout is deliberately “hexagonal”:

- **Core kernel:** `LogOS/LT/**` — what a logical transformer *is* (kernel + refinement + composition).
- **Ports (interfaces):** `LogOS/Ports/**` — named boundary interfaces (observation, I/O, opacity, …).
- **Adapters (implementations):** `LogOS/Adapters/**` — concrete implementations of ports.
- **Apps (“macro packs”):** `LogOS/Apps/**` — composed case studies, kept out of the kernel.
- **Curated API:** `LogOS/API/**` — stable entrypoints for downstream use.

The import direction is enforced by CI (see `scripts/check/layer_order_check.sh` and `docs/Core/Architecture/Diagram.lagda.md`):
outer layers (API/Apps/Adapters/Ports) may import inner layers (LT/Syntax/Prelude/Host), never the other way around.

Guardrails and “tight CI” philosophy
------------------------------------

<!-- CLAIM-STAMP: DERIVED | anchor=Makefile#check-all -->

LogOS treats policy as part of correctness.

Run:

- policy lane: `make check-policy`
- core Agda lane: `make check-core`
- integration Agda lane: `make check-integration`
- docs lane: `make check-docs`
- library smoke lane: `make check-lib`
- cold/full gate: `make check-all`
- dev toolchain notes: `docs/Core/Orientation/Dev_Environment.lagda.md`

Authoritative references (keep these as the only policy/guardrails sources):

- guardrails + “what this does not claim”: `docs/Core/Spec/LogOS_Specification.lagda.md`
- checks enforced by `make ci-policy` (generated): `docs/Generated/Policy_Index.md`
- optional doctrines (explicit parameters, never ambient): `docs/Core/Meta/Assumptions_Ledger.md`
- documentation honesty discipline: `docs/Core/Meta/Claim_Stamps.md`

Applications (packs)
--------------------

<!-- CLAIM-STAMP: DEFINITION | anchor=docs/Patterns/HowTo/HowTo_Add_App.lagda.md#how-to-add-an-application-pack -->

Application packs live under `LogOS/Apps/**`.
Implemented packs have a `LogOS/Apps/*/All.agda` entrypoint that includes a short audited story block
(`Entrypoints:`, `Implemented now:`, `Planned:`). Planned packs should be tracked in separate project planning
docs (we avoid empty pack directories until code exists).

- **Opacity** (minimal demo implemented; broader pack planned): boundary-as-interface and information hiding.
  - Pack: `LogOS/Apps/Opacity/All.agda`
  - Demo entrypoint: `LogOS/Apps/Opacity/Demo.agda`
- **ZFC compatibility** (implemented): ZF/ZFC as a stack of logical transformers with an explicit boundary.
  - Pack: `LogOS/Apps/ZFC/All.agda`
  - Primary interface: `LogOS/Apps/ZFC/Stack.agda`
  - Curated tower packaging: `LogOS/Apps/ZFC/Stack/ReifiedTower.agda`
- **Concurrency** (minimal pack implemented): causality as boundary closure (happens-before example).
  - Pack: `LogOS/Apps/Concurrency/All.agda`
  - Example entrypoint: `LogOS/Apps/Concurrency/HappensBefore.agda`
- **Physics** (minimal pack implemented): small measurement-style example (outcomes as a preorder; opacity/pullback reading).
  - Pack: `LogOS/Apps/Physics/All.agda`
  - Example entrypoint: `LogOS/Apps/Physics/MeasurementExample.agda`
- **Conversation** (planned): multi-turn dialogue traces as transformer structure.
  - Tracked in external project planning docs (no pack directory until code exists)
- **Universality** (implemented): computation/universality as a transformer application.
  - Pack: `LogOS/Apps/Universality/All.agda`
- **Turing categories (CH2008)** (implemented core, planned extensions): restriction-category interfaces, a canonical
  partial-map model, and observation-induced bridges, phrased in the refinement-first discipline (CT-shaped, distinct
  from CTD).
  - Pack: `LogOS/Apps/TuringCategory/All.agda`
- **Transformer architecture** (planned): model transformer-like systems and LLM artefacts as transformer structure.
  - Tracked in: `docs/Core/Project/Design_Goals.md` (no pack directory until code exists)
- **Analytic S-matrix** (planned, low priority): late-stage axiomatic application.
  - Tracked in: `docs/Core/Project/Design_Goals.md` (no pack directory until code exists)

The generic shared-boundary / many-realisations pattern is part of the ports layer,
not a standalone application pack. See `LogOS/Ports/Realisations/DependentStack.agda`,
`LogOS/Ports/Realisations/Architecture.agda`, and
`docs/Interpretations/Applications/Application_Sketches.lagda.md`.

API entrypoint
--------------

For downstream code that wants the “kernel surface”, import:

- `LogOS/API/LT.agda`

It gathers the core kernel (`LogOS/LT/**`) plus selected ports (`LogOS/Ports/**`) in one entrypoint.
It also provides the optional valuation/numerics surface (`LogOS/API/Valuation.agda`) for explicit budget/time modelling.

Locality-facing note (v1.1): the curated API is **dependent-first** (ultralocal by default).
Uniform (constant-family) usage is expressed inline by taking constant families
(`O = λ _ → O₀`, `GC₀ = λ _ → GC₀₀`) against the same dependent-first port surface.
