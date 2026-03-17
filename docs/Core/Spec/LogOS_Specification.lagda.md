<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS LT — Specification (v1.1, literate)

This file is the **implementation-facing specification** for LogOS 1.1.
It is intended to be readable on its own, while staying mechanically honest:
every module path referenced as “implemented” is imported in the sync-guard block below, so drift breaks the
docs build.

Design-target mathematical specification (literate, typechecked):

- `docs/Core/Spec/LogicalTransformers.lagda.md`

Companion doc (mechanisation status / module map):

- `docs/Core/Spec/Implementation_Map.lagda.md`

```agda
{-# OPTIONS --safe #-}
module docs.Core.Spec.LogOS_Specification where

-- Sync guard: if these move/rename, `make check-all-docs` fails.
import LogOS.Prelude
import LogOS.Syntax.Prop

import LogOS.LT.ConPreorder
import LogOS.LT.FunPreorder
import LogOS.LT.View
import LogOS.LT.Kernel
import LogOS.LT.Hom
import LogOS.LT.Iteration
import LogOS.LT.Stack

import LogOS.LT.Thin2Cat
import LogOS.LT.Thin2Functor
import LogOS.LT.DisplayedThin2Cat

import LogOS.LT.LOG.Kernel2Cat
import LogOS.LT.LOG.Contract2Cat
import LogOS.LT.LOG.EncodePort2Cat
import LogOS.LT.Flow
import LogOS.LT.HomFlow
import LogOS.LT.LOG.Flow2Cat
import LogOS.LT.LOG.ArchitectureFlowContract2Cat
import LogOS.LT.Sup.FinSup
import LogOS.LT.Sup.AbstractSigmaDCPO
import LogOS.LT.Sup.SupOmega
import LogOS.LT.Sup.AbstractKleene
import LogOS.LT.Sup.AbstractCoKleene
import LogOS.LT.Reflection
import LogOS.LT.Contracts
import LogOS.LT.InstitutionFragment
import LogOS.LT.PredicateReindexing
import LogOS.LT.AbstractKZ
import LogOS.LT.Derivability
import LogOS.LT.Presentation
import LogOS.LT.Presentation.Independence

import LogOS.LT.Presentation.ObservationInitiality
import LogOS.LT.Presentation.ExtensionalMinimality
import LogOS.LT.Theorems.ArchitecturalNormalForm
import LogOS.LT.Theorems.ExtensionalReflection
import LogOS.LT.Theorems.EvaluatorReflection
import LogOS.LT.Presentation.Transport
import LogOS.LT.Presentation.Interlingua
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic

-- Systems-facing ports (hexagonal boundary layer).
import LogOS.Ports.IO
import LogOS.Ports.Opacity

-- Curated downstream entrypoint.
import LogOS.API.LT

-- Explicit optional surface: the opacity pack is intentionally not re-exported
-- by `LogOS.API.LT`, but the implementation-facing spec still tracks it.
import LogOS.API.Opacity

-- Explicit optional surface: reification-specific theorem layers stay opt-in
-- and are therefore tracked separately from `LogOS.API.LT`.
import LogOS.API.Reification

-- App-level examples tracked by this spec narrative.
import LogOS.Apps.Opacity.Demo
import LogOS.Apps.ZFC.Stack
```

Status and scope
----------------

<!-- CLAIM-STAMP: DEFINITION | anchor=LogOS/LT/Kernel.agda#Kernel -->

This specification is **v1.1 kernel-first**:

- It specifies the core mathematical object: a **logical transformer kernel** with an explicit boundary.
- It specifies the repository’s discipline: refinement-first, safe, stdlib-independent, host-minimal.
- It treats “ports/adapters/apps” as architecture: ports are *interfaces*; adapters are *implementations*;
  apps are *case studies* that must not leak into the core.

This document is **not** a claim that every part of the design-target spec is mechanised already.
When something is described as “planned”, it means it is described in `docs/Core/Spec/LogicalTransformers.lagda.md`
but is not yet fully implemented in the Agda library; mechanisation status is tracked in
`docs/Core/Spec/Implementation_Map.lagda.md`.

Spine of construction (self-similar)
------------------------------------

The spec is organised around a single construction path; every “port category” is a presentation of this path:

- `ConPreorder` → `View` → `Kernel` → `KernelHom`
- `LOG` as a thin 2-category of kernels
- `DisplayedThin2Cat` as the port interface
- `DecoratedThin2Cat` as the decorated category
- `ProductDisplayed` for independent port composition
- law-ports with explicit forgetful projections

Architecture view (tetrahedron reading)
---------------------------------------

There is one particularly clean repository reading of this spine:

- **equator:** preserved observational comparison world `LOG`,
- **construction apex:** presentation/program growth over a fixed boundary
  (stacks, programs, presentations),
- **discipline apex:** displayed/port growth (contracts, flow, quotation, …),
  totalised by Σ (`DecoratedThin2Cat`),
- **realisation apex:** one shared boundary together with many realisation
  families over it.

In this reading, “faces commute” **by local refinement** (`⊑` / public-facing alias `≼`, plus `≈`) by
default, not by strict equality (`≡`). Strictness is an explicit opt-in check
or reflective collapse (e.g. via classical-limit strictification in the
supported fibres).

This primary typed view is documented (as a view, not a new axiom) in:

- `docs/Core/Architecture/Tetrahedron.lagda.md`

and is also packaged as typed structure (packaging only; no new semantics):

- `LogOS/LT/Architecture/Tetrahedron.agda` (primary packaging)
- `LogOS/LT/Architecture/LogOS.agda` (canonical LT construction/discipline face)
- `LogOS/API/Architecture.agda` (curated public surface for the story)

The bi-pyramid remains as the derived construction/discipline face:

- `docs/Core/Architecture/BiPyramid.lagda.md`
- `LogOS/LT/Architecture/BiPyramid.agda`

The generic physics-facing pattern is the shared-boundary / many-realisations
realisation corner over a fixed shared distributed-semantics ledger
(`LogOS/Ports/Realisations/DependentStack.agda`,
`LogOS/Ports/Realisations/Architecture.agda`).

One downstream design target is the **Deutsch-style category**: a port stack
over that same ledger (locality + causality + local reversibility). Local
reversibility is implemented as pointwise order-isomorphisms and is
intentionally weaker than unitarity; local unitarity is planned as a
refinement (`LogOS/Ports/AbstractDeutsch2Cat.agda`, parameterised by
`DependentLocalSemantics`; the uniform case is recovered by choosing constant
families of observables and doctrine).

This organisation is deliberately self-similar: the code that implements ports and port categories is itself
a presentation of the categorical construction (displayed structure + totalisation).

The key engineering stance is that *meaning* is not derived from self-reference. Meaning is injected only at
explicit points: a `View`/`Kernel` fixes `decode` (observable semantics), and packs such as
`DependentLocalSemantics` fix a shared semantics for downstream constructions.

Capstone packaged theorem
-------------------------

The implementation-facing capstone theorem is:

- `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`

It packages the current mechanised LT core as one positive statement:

- observation forces the canonical pullback refinements for views and probe suites;
- façade morphisms factor through boundary transport plus displayed
  implementation;
- Σ-totalisation inherits refinement/equivalence from the base alone;
- the supported LT layers are definitionally displayed/totalised;
- strict collapse appears only through explicit strictification constructions.

The public witness is `architecturalNormalForm :
ObservationPreservingArchitecturalNormalForm …`.

Detailed theorem-member inventory and status tracking live in:

- `docs/Core/Spec/Implementation_Map.lagda.md`

Pedantic boundary: this theorem does **not** prove a meta-level absence result
such as “strict collapse is impossible”. Its formal content is positive:
the refinement bundle stays equality-free, while strictification is supplied
only by the companion `LogOS/LT/Theorems/ArchitecturalNormalFormStrictification.agda`
surface.

The implementation also now packages a second theorem surface:

- `LogOS/LT/Theorems/ExtensionalReflection.agda`

Its content is again positive and relative: inside each explicitly
classical-limit-equipped fibre over a displayed doctrine `D`, the
observation-first fibre reflects into its extensional subfibre by
`strictifyFiber`, with inclusion `includeExtensional` and homwise universal
property `homwiseExtensionalReflection`.

At full repository level, these two LT theorem surfaces are now bundled with
the LogicArchitecture metatheory theorem:

- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda`

Its primary aliases are:

- `MechanisableLogicWorld`
- `mechanisableLogicWorld`
- `MechanisableBoundarySemanticsTheorem`
- `mechanisableBoundarySemanticsTheorem`

This is the current repository-level mechanised answer to “what is this logic?”:

- explicit boundary semantics fixes a canonical thin refinement world,
- each hom of that world is canonically an LT kernel, and complete
  presentations over the same boundary semantics recover that kernel’s
  canonical preorder,
- guarded evaluator reflection and guarded Lawvere-style self-reference are
  internal projections of that same world,
- and extensionality appears only as explicit reflective collapse inside
  classical-limit fibres.

What this does *not* claim {#what-this-does-not-claim}
------------------------------------------------------

<!-- CLAIM-STAMP: DERIVED | anchor=docs/Core/Spec/LogOS_Specification.lagda.md#what-this-does-not-claim -->

This specification is intentionally **weak** and therefore prone to over-reading.
It does *not* claim (by default) that:

- `decode` is *complete* for some intended operational/denotational semantics (you must model and justify that
  separately, per application).
- `decode` is injective, or that observational equivalence/refinement implies Agda equality of code.
- refinement captures intensional properties like cost, termination, or step-by-step trace fidelity (those belong
  to optional ports/doctrines/packs).
- a boundary comes with a distinguished closure (`Flow`) and/or completeness structure (finite joins `FinSup`,
  σ-directed ω-suprema `SigmaDCPO`) unless those are supplied explicitly.
- every part of the design-target spec is already mechanised (items marked “planned” are not).
- the repo identifies strict equality with the default semantics of morphisms or
  2-cells; the mechanised capstone theorem instead packages explicit
  strictification constructions over a refinement-first core
  (`LogOS/LT/Theorems/ArchitecturalNormalForm.agda`).

Non-negotiable build constraints (philosophy as policy)
------------------------------------------------------

<!-- CLAIM-STAMP: DERIVED | anchor=Makefile#ci-policy -->

The library is pinned to the following constraints:

- **No stdlib dependency:** typechecking uses `--no-libraries` (see `Makefile`).
- **Safe surface:** every module and literate module opts into `{-# OPTIONS --safe #-}` (see
  `scripts/check/safe_options_check.sh`).
- **Warnings-as-errors:** CI runs with strict warnings (`-W all -W error`, see `Makefile`).
- **Host-minimal:** only `LogOS/Host/**` may import `Agda.Primitive` or `Agda.Builtin.*` (see
  `scripts/check/host_import_check.sh` and `docs/Core/Architecture/Diagram.lagda.md`).
- **No axioms by default:** `postulate` is forbidden except an explicit allowlist with a justification block
  (see `scripts/check/postulate_policy_check.sh`).
- **No “meaning injection bypass”:** pointwise boundary primitives (`LocalBoundary`, `FunPreorder`/`DFunPreorder`) are
  quarantined behind the explicit locality injection points, so changing meaning requires an explicit bridge
  (`scripts/check/local_boundary_usage_check.sh`, `scripts/check/local_boundary_map_check.sh`, `scripts/check/agda_policy_bundle_check.sh`).
- **Refinement-first theorem surface:** theorem statements are stated in refinement/mutual refinement (not `≡`) and are
  checked mechanically (`scripts/check/agda_policy_bundle_check.sh`, see `docs/Generated/Policy_Index.md`).
- **Unicode hygiene:** forbid invisible / bidi control characters in source and docs (Trojan Source style footguns)
  (`scripts/check/unicode_invisibles_check.sh`).

These are not “lint”; they are part of the intended semantics story: LogOS must be auditable and
transportable as a small, stable kernel.

S/G/H discipline (relation stance)
----------------------------------

LogOS separates three tiers:

- **S-tier (strict):** use propositional equality `≡` only for data/coherence/bookkeeping.
- **G-tier (refinement):** use one directed refinement preorder `⊑` as the primary judgement; on explanatory surfaces this may be written `≼`; derive mutual
  refinement `≈` as `(x ⊑ y) × (y ⊑ x)`.
- **H-tier (guarded):** treat assumption-scoped judgements as *boundary constraints as guards*.

The core carrier for “specification spaces” is:

- constrained preorders: `LogOS/LT/ConPreorder.agda`

The refinement polarity is “stronger is larger”: `c ⊑ d` reads “`d` refines/entails `c`”.
On public-facing explanatory surfaces, the same refinement judgement may also be written `c ≼ d`.

Views, pullbacks, and presentation-independence
-----------------------------------------------

Any presentation-dependent relation should be defined by an explicit readout:

- views: `LogOS/LT/View.agda`

The guiding rule is:

> If you cannot name the view/probe that induces your relation, you probably should not be adding a new
> primitive relation to the core.

LogOS makes this “presentation independence” precise:

- A **presentation** of a view `V` is a preorder `≼` equipped with a proof that each step respects
  observation (`x ≼ y → x ⊑[ V ] y`). This is `LogOS.LT.Presentation.Presentation`.
- The **canonical** presentation is the pullback refinement along `V` itself (`x ⊑[ V ] y`), and every
  observation-respecting presentation refines into it (`Presentation.toCanonical` in `LogOS/LT/Presentation.agda`).
- A presentation is **complete** if it also derives every semantic refinement (a `CompletePresentation` witness).
  Soundness + completeness yields an equivalence with the canonical refinement (`presentation↔canonical`).
- Therefore any two complete presentations for the same view are equivalent: the choice of presentation cannot
  change meaning, it only changes the internal derivation interface
  (`presentationsAgree` in `LogOS/LT/Presentation/Independence.agda`).

For “many probes” (locality-style observation families), the same maximality story is proved for probe suites:
any relation respecting every probe is contained in the induced suite refinement
(`SuiteForced` / `SuiteForcedᵈ` in `LogOS/LT/Presentation/ObservationInitiality.agda`).

Design reading (derived; theorems above are the formal content): much of what is often treated as additional
“architecture choice” collapses to the choice of **observables**.
Once you commit to a view/probe suite, the coarsest admissible refinement respecting it is forced by pullback,
so there is no need (and little room) for an extra ad-hoc “implementation relation”.

This observation-forcedness result is one pillar of the bundled theorem
`ObservationPreservingArchitecturalNormalForm`; the other pillars are façade
factorisation through `BoundaryHom × BoundaryImplementation`, displayed
totalisation normal forms for the supported LT layers, and explicit late
strictification.

App-level extension (outside the v1.1 kernel): the same forcedness principle is mechanised for homwise
observations of 2-cell presentations (contextual shadows) in the LogicArchitecture pack; see
`docs/Core/MetaTheory/Observation_Controlled_Approximation.lagda.md`.

Kernels: boundary + code + decode
---------------------------------

The core “component” notion is a kernel:

- `LogOS/LT/Kernel.agda`

Normatively, a kernel `K` exposes:

- a boundary constraint preorder `bnd(K) : ConPreorder` (the interface);
- a code type `Code(K) : Set` (internal representation);
- a decoder/evaluator `decode : Code(K) → Con (bnd(K))` (canonical boundary readout).

The key non-choice (forced by the view discipline) is:

> The code preorder is the pullback order induced by decoding.

This stance is proved as an “extensional minimality” principle:

- `LogOS/LT/Presentation/ExtensionalMinimality.agda`

Kernel morphisms and observational refinement (2-cells)
-------------------------------------------------------

Kernel morphisms are the adapter/wiring notion:

- `LogOS/LT/Hom.agda`

Normatively, a kernel morphism `h : K → K'` carries:

- a boundary map `map∂ : Con (bnd K) → Con (bnd K')` (covariant, monotone);
- a code map `mapCode : Code K → Code K'`;
- a literal architecture/implementation split in code: `BoundaryHom` carries the boundary transport, `BoundaryImplementation` carries the displayed implementation/coherence layer, and `KernelHom` is the stable façade that combines them;
- refinement-first `decode` coherence (S-tier evidence, not an axiom): decoding commutes with the morphism up to mutual refinement (`≈`), i.e.
  `decode (mapCode γ) ≈ map∂ (decode γ)`.
- strict `decode` coherence (`≡`) only under the explicit `LogOS.API.Strictification` surface, available via an explicit antisymmetry-based strictification assumption (`LogOS/Ports/ClassicalLimit.agda`).

The 2-cell refinement between parallel morphisms is **observational**: it compares morphisms pointwise only after mapping into the boundary preorder, not by raw code-level structure.
In v1.1 there is one canonical pullback refinement on kernel morphisms and one equivalent derived presentation:

- boundary-driven refinement (`_⇒∂_`): pullback along `transportView` (transport `decode` along `map∂`)
- implementation-first refinement (`_⇒_`): pullback along `obsView` (run `mapCode` then `decode`); this is retained as an explicit derived view rather than the flat default API

They are equivalent by the `decode-mapCode : ≈` coherence (bridge lemmas in `LogOS/LT/Hom.agda`). The guarded `under` mode is surfaced separately through `LogOS.API.Guarded`, while strict equality-based views live only under `LogOS.API.Strictification`.

Thin 2-categories (`LOG`) and functoriality
-------------------------------------------

The kernel packages into a thin 2-category:

- thin 2-category interface: `LogOS/LT/Thin2Cat.agda`
- thin 2-functors: `LogOS/LT/Thin2Functor.agda`
- kernel instance: `LogOS/LT/LOG/Kernel2Cat.agda`

Objects are kernels, 1-cells are kernel morphisms, and 2-cells are boundary-driven observational refinements (`_⇒∂_`).

Ports as displayed layers (hexagonal architecture in math form)
---------------------------------------------------------------

The port/adapters story is made compositional by a single decision:

- decision doc: `docs/Patterns/Ports_As_Displayed.lagda.md`
- implementation: `LogOS/LT/DisplayedThin2Cat.agda`

Normatively:

- Architecture is `LOGᴳ`: kernels plus boundary transport and boundary-only refinement.
- Implementation is the displayed layer `ImplementationDisplayed` over `LOGᴳ`, totalised as `LOGᴳʳ`.
- The preserved façade is `LOG`, reached by weakening `toLOG : LOGᴳʳ → LOG`.
- A **law port** is further displayed structure layered over one of those preserved bases.

Crucial guardrail:

> Refinement of total morphisms is inherited from the base `LOG` morphism only.
> Port obligations do not participate in the hom-preorder, so ports cannot collapse refinement into equality.

Canonical port layers already in the core:

- Contracts as a displayed layer: `LogOS/LT/LOG/Contract2Cat.agda`
- Encode port as a displayed layer: `LogOS/LT/LOG/EncodePort2Cat.agda`
- Flow/closure as a displayed layer: `LogOS/LT/LOG/Flow2Cat.agda`
- Example of architecture-first port composition (Flow + Contract): `LogOS/LT/LOG/ArchitectureFlowContract2Cat.agda`

Contracts: boundary as a logic of kernels
-----------------------------------------

Boundary constraints are treated as a logic *about* kernels.
This is implemented by contract packaging:

- contract interface + satisfaction: `LogOS/LT/Contracts.agda`
- contract thin 2-category (displayed over `LOG`): `LogOS/LT/LOG/Contract2Cat.agda`

Engineering reading: a contract is “component + requirement”.
Categorical reading: this is a Σ-totalisation (category-of-elements-style; refinement inherited from the base, displayed evidence ignored) over the boundary fiber.

Institution-fragment and predicate-reindexing views (optional packaging)
------------------------------------------------------------------------

LogOS exposes two explicit optional view modules for the contract layer:

- institution fragment packaging: `LogOS/LT/InstitutionFragment.agda`
- predicate-fiber reindexing fragment: `LogOS/LT/PredicateReindexing.agda`

These are derived views of the same underlying kernel + contract story; they
do not introduce new axioms.

Pedantic boundary:

- `InstitutionFragment` is a covariant institution fragment, not a full textbook
  institution. Its `sat-condition` is forward preservation, and the classical
  contravariant variance is recovered by taking opposites.
- `PredicateReindexing` is only the reindexing fragment: no quantifiers, no
  comprehension, no Beck–Chevalley, and no cleavage interface.

Flow (guarded closure), stability, and normalisation doctrine
-------------------------------------------------------------

The design-target spec treats normalisation/stabilisation as guarded closure on the boundary:

- closure interface: `LogOS/LT/Flow.agda`
- flow-preserving morphisms: `LogOS/LT/HomFlow.agda`
- flow-equipped thin 2-category: `LogOS/LT/LOG/Flow2Cat.agda`

Normatively, a `Flow` is a closure-like operator on boundary constraints (a closure operator on a preorder,
idempotent up to mutual refinement) with monotonicity and the closure laws stated in refinement form (`⊑`, or `≼` on explanatory surfaces),
not as strict equalities (`≡`).

The compositionality requirement is a single inequality (“lax naturality”):

> boundary transport commutes with closure up to refinement.

Reflection and partial self-reference (fixed points)
----------------------------------------------------

Reflection is treated as a typed, assumption-scoped construction through stable points:

- stable points and quotation/evaluation: `LogOS/LT/Reflection.agda`
- σ/ω-style completeness interfaces (optional): `LogOS/LT/Sup/`
- evaluator reflection theorem bundle: `LogOS/LT/Theorems/EvaluatorReflection.agda`

Design stance:

- Reflection is not meta-level argumentation; it is boundary-level structure plus explicit closure witnesses.
- Self-reference is partial and guarded: it appears only through fixed points/stability interfaces.

Iteration and “stacks of transformers”
--------------------------------------

Two implementation-facing macro principles:

- iteration/guard modality lemmas: `LogOS/LT/Iteration.agda`
- stacks: “a stack of transformers is a transformer”: `LogOS/LT/Stack/Core.agda` (and `LogOS/LT/Stack.agda` publishes the full stack surface)

These are the bridge to application packs: they let apps build domain-specific macro languages while keeping
the kernel small.

Ports (hexagonal boundary layer): I/O and opacity
-------------------------------------------------

The ports under `LogOS/Ports/**` are the systems-facing boundary interface layer:

- I/O + telemetry port: `LogOS/Ports/IO.agda`
- opacity/observational interface port: `LogOS/Ports/Opacity.agda`

These are ordinary records/interfaces (not displayed layers) because they are intended as hexagonal
“ports” in the engineering sense: stable interfaces for adapters and apps.

Curated API surface
-------------------

Downstream code should prefer importing:

- `LogOS/API/LT.agda`

It gathers the stable kernel modules and selected ports, keeping app-level experiments out of the core.

Applications (examples, not dependencies)
-----------------------------------------

Apps are explicitly *not* part of the kernel, but they serve as regression tests for the architecture:

- Opacity demo: `LogOS/Apps/Opacity/Demo.agda` (pack doc: `LogOS/Apps/Opacity/All.agda`)
- ZFC stack interface: `LogOS/Apps/ZFC/Stack.agda` (pack doc: `LogOS/Apps/ZFC/All.agda`)

Apps must not be imported by `LogOS/LT/**` or `LogOS/Ports/**` (enforced by `scripts/check/layer_order_check.sh`).

Mechanisation status
--------------------

For the single authoritative mapping of “implemented vs planned (and where)”, see:

- `docs/Core/Spec/Implementation_Map.lagda.md`
