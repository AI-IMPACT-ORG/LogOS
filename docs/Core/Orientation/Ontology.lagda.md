<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Engineering lexicon (LogOS LT)

This library is intentionally *both* a mathematical kernel and a systems-engineering library.
This page standardises the “engineering reading” of the core words.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Orientation.Ontology where

import LogOS.API.LT
```

## Audit pointers

- Audit guide (workflow): `docs/Core/Orientation/Audit_Guide.lagda.md`
- Design-target spec (definitions/theorem spine): `docs/Core/Spec/LogicalTransformers.lagda.md`
- Claim stamps (format + intent): `docs/Core/Meta/Claim_Stamps.md`
- Claim stamp index (generated): `docs/Generated/Claim_Stamp_Index.md`
- Terminology policy (canonical wording): `docs/Patterns/Terminology_Policy.lagda.md`
- High-risk conventions: `docs/Core/Orientation/High_Risk_Conventions.lagda.md`

## Quick disambiguations

Use this section only for the high-frequency names that recur in this glossary.
For the full outward-facing naming table, use
`docs/Patterns/Terminology_Policy.lagda.md`.

- `Thin2Cat`: read as a locally preordered 2-category.
- `KernelHom`: read as boundary transport plus a displayed realiser.
- `ClassicalLimit`: read as antisymmetry-based strictification, not ambient classical logic.
- `ObservedCodePreorder`: read as the observational/code preorder induced by `decode`, not as a primitive operational order.
- `DependentLocalSemantics` / `PhysicalTransformers`: read as the shared distributed-semantics ledger plus its locality-indexed transport tooling.
- `QAdapter`: read as a valuation algebra / quantitative adapter.
- `PreQuantum`: read as prequantum / CQM-style structure, not full quantum mechanics.

## Core nouns

- **`ConPreorder`**: an *interface/specification space* of constraints, ordered by refinement/entailment.
  - carrier `Con`: interface constraints / requirements / observable specs
  - order `c ⊑ d`: “`d` refines/entails `c`” (stronger constraints are larger)
  - public-facing alias `c ≼ d`: the same refinement relation, used only when the `⊑` polarity would otherwise be easy to misread
  - notation convention (docs): we often elide `Con` in prose, writing `c : O` for `c : Con O` and
    the following shorthands for pointwise/distributed boundaries:
    - `I → O₀` for the **uniform** boundary `FunPreorder I O₀` (carrier `I → Con O₀`),
    - `Π i → O i` for the **dependent** boundary `DFunPreorder I O` (carrier `(i : I) → Con (O i)`).
- **`View X O`**: an explicit *probe/sensor/readout* from internal state `X` into an observation interface `O`.
  - all presentation-dependent relations on `X` should be defined by pullback along an explicit `View`
- **Presentation (`LogOS/LT/Presentation.agda`)**: a *proof/syntax layer* behind a fixed view.
  - a `Presentation V` is any preorder on `X` whose steps are monotone w.r.t. the observable meaning induced by `V`
  - terminology note: other docs may say “(boundary) presentation” informally to mean “a kernel presenting a boundary”
    (code + `decode`); the `Presentation` record is specifically the proof-theoretic layer.
- **Probe suite (`ProbeSuite X I O₀`)**: a *family of probes* `I → View X O₀` (think “telemetry channels”).
  - the combined readout is `suiteView : View X (FunPreorder I O₀)` and refinement is the pullback along it
  - representation theorem (uniform): probe suites and distributed views are the same data, pointwise on observations:
    `ProbeSuite X I O₀` ↔ `View X (FunPreorder I O₀)` (`LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`)
    - packaged as a μ-level equivalence record: `ProbeSuiteViewEquiv` / `probeSuiteViewEquiv`
- **Dependent probe suite (`DependentProbeSuite X I O`)**: a *family of probes* `(i : I) → View X (O i)`.
  - the combined readout is `suiteViewᵈ : View X (DFunPreorder I O)` and refinement is the pullback along it
  - representation theorem (dependent): dependent probe suites and distributed views are the same data, pointwise on observations:
    `DependentProbeSuite X I O` ↔ `View X (DFunPreorder I O)` (`LogOS/LT/Theorems/DependentProbeSuiteRepresentation.agda`)
    - packaged as a μ-level equivalence record: `DependentProbeSuiteViewEquiv` / `dependentProbeSuiteViewEquiv`
  - minimality/initiality: observation forces the coarsest admissible refinement (`SuiteForcedᵈ` in
    `LogOS/LT/Presentation/ObservationInitiality.agda`)
- **Locality port (`LogOS/Ports/Locality/Core.agda`)**: a *local observation decomposition* (canonical by design for v1.1).
  - a dependent locality port is a dependent probe suite, packaged for “ultralocal-first” modelling
  - shared boundary = dependent pointwise interface `LocalBoundary I O = DFunPreorder I O`
  - canonical constructor `localKernel` makes “a local observation family is a kernel” precise
  - uniform special case: take a constant family `O = λ _ → O₀`
- **Realisation family (`LogOS/Ports/Realisations/DependentStack.agda`)**: a *generic shared-boundary / many-realisations pattern*.
  - choose shared distributed semantics through `DependentLocalSemantics`
  - package each realisation as a locality port / kernel over that shared boundary
  - downstream packs may specialise this pattern, but the primitive surface is the shared-boundary pattern itself
- **Kernel (`LogOS/LT/Kernel.agda`)**: a *component* with an explicit boundary interface.
  - `bnd`: the boundary/interface spec space
  - `Code`: internal representation (program, circuit, graph, trace, …)
  - `decode : Code → Con bnd`: the canonical boundary readout (“what the component means at the interface”)
  - `kernelFromView : View X O → Kernel …` packages a named observation as a kernel (decode-first discipline)
  - `EncodePort`: optional port `encode : Con bnd → Code` (compile / synthesise code from boundary specs)
- **Pack / application pack (`LogOS/Apps/**`)**: a *domain instantiation* of the kernel + ports.
  - packs name designer choices (boundary/closure vocabularies) and expose irreducible obligations as records (“ledgers”)
  - packs are intentionally **not** part of the curated core API (`LogOS/API/**`)
  - the docs use “pack” and “app” interchangeably; the code location is authoritative (`LogOS/Apps/**`)
- **Kernel morphism (`KernelHom`)**: an *adapter/wiring harness* between components.
  - `map∂`: transport boundary constraints on the boundary side
  - `mapCode`: transport internal representations on the code side
  - default `decode` coherence is by **mutual refinement** (`≈`): decoded meaning commutes with wiring up to
    observational equivalence (`decode(mapCode γ) ≈ map∂(decode γ)`)
  - strict `decode` coherence (`≡`) is quarantined to the explicit `LogOS.API.Strictification` surface and
    requires an explicit antisymmetry-based strictification assumption/port (`LogOS/Ports/ClassicalLimit.agda`)
  - optional `encode` coherence (`EncodeCompat`): says compilation ports commute with wiring (encode as an explicit port layer:
    `LogOS.LT.LOG.EncodePort2Cat.WithPort`)
- **`LOG`**: the thin 2-category (LogOS sense: a locally preordered 2-category) of kernels.
  - objects: kernels
  - 1-cells: kernel morphisms
  - 2-cells: boundary-driven observational refinements (`_⇒∂_` in base `LOG`; realiser-first `_⇒_` is equivalent)
- **Displayed structure (`DisplayedThin2Cat`)**: a *port layer* over a base thin 2-category (typically `LOG`).
  - displayed objects: per-kernel configuration (ports/guards/doctrines)
  - displayed morphisms: per-adapter compatibility obligations
  - totalisation: builds the decorated component graph, while keeping the same underlying observational refinement
  - scope note: this is displayed-category/Σ-totalisation packaging; v1.1 does not model cartesian lifts/cleavages
    (see `docs/Patterns/Clarifications/Displayed_Structure_vs_Fibrations.lagda.md`)
- **Port composition (`PortStack`)**: stack independent port layers over the same base without coupling them.
  - `PortStack` is the typed wrapper (capability projections + forgetting); it folds definitionally to a right-associated
    `ProductDisplayed`.
- **Contract (`mkContract K c`)**: a *component+requirement bundle* (“K must satisfy boundary constraint c”).
  - satisfaction is purely interface-level: `c ≼ decode γ`
- **Contract port category (`LogOS.LT.LOG.Contract2Cat.WithPort`)**: contracts (“kernels with a chosen boundary guard”).
  - engineering reading: *requirements flow along adapters*
  - categorical reading: Σ-totalisation (category-of-elements-style; refinement inherited from the base, displayed evidence ignored) of the boundary fiber
- **Flow / guarded closure**: a *normaliser/stabiliser* on boundary specs (μ-calculus flavour).
  - `Flow` is monotone + inflationary + lax-idempotent
  - stable points package “stabilised specs” as explicit witnesses (`Stable`)
  - optional: if the boundary has finite meets and `Flow` preserves them, you can upgrade to a locale-style nucleus:
    `LogOS/LT/AbstractNucleus.agda` (`Nucleus`)
- **Stable completion (quine step)**: a canonical factorisation into stable points induced by a chosen closure.
  - for any `K` and `GC : GuardedClosure (bnd K)`, there is a canonical adapter
    `K → quoteKernel GC` with a judgmental-after-unfolding law, hence `≈` by reflexivity
    :
    `decode(mapCode γ) ≈ Flow(decode γ)`
  - mechanised as wiring over `effectivise` and `quot`: `LogOS/LT/Theorems/StableCompletion.agda`
- **σ-completeness layer (`LogOS/LT/Sup/`)**: optional algebra/completeness on boundaries.
  - finite joins + bottom (`FinSup`), read as finite aggregation/conjunction on constraints
  - σ-directed ω-suprema (`SigmaDCPO`) with explicit upper-bound + leastness witnesses
  - derived ω-sup summary `supω` (prefix-join construction), used by `LogOS/LT/Iteration.agda` (`run`)
  - optional σ-(co)continuity + μ/ν fixed point spines:
    `LogOS/LT/Sup/AbstractSigmaDCPO.agda` (`SigmaContinuous`), `LogOS/LT/Sup/AbstractKleene.agda`, `LogOS/LT/Sup/AbstractCoKleene.agda`
- **Residuals / residuation (`L ⊣ R`)**: an adjoint/Galois-connection nugget that induces canonical completion.
  - right adjoint `R` can be read as “weakest precondition / right-adjoint back-translation”
  - induced closure (nucleus-style) is `Flow = R ∘ L` (see `LogOS/LT/Theorems/AbstractGaloisConnection.agda`, vocabulary wrapper `LogOS/Ports/Residuals.agda`)
- **Causality port (`LogOS/Ports/Causality.agda`)**: *causal vocabulary for Flow* (Flow-side naming only).
  - in v1.1, “causal” means “equipped with a guarded closure on the boundary”
  - “causal translation” means a flow-preserving adapter (`KernelHomFlow`)
  - design note: for the shared distributed-semantics discipline, prefer a *shared* closure/law (fixed once per semantics), see `docs/Patterns/Shared_Distributed_Semantics.lagda.md`
- **Flow-preserving morphism (`KernelHomFlow`)**: an adapter compatible with stabilisation.
  - coherence: `map∂ (Flow c) ≼ Flow (map∂ c)`
  - packages the “lax naturality” needed to make Flow compositional across translations
- **Flow port category (`LogOS.LT.LOG.Flow2Cat.WithPort`)**: flow-equipped components and flow-preserving adapters.
  - capability-first projection pattern: use `PortStack.baseObj` with `LogOS.LT.LOG.Flow2Cat.stack` for the underlying kernel,
    and `PortStack.getObj LogOS.LT.LOG.Flow2Cat.port` for the closure payload.
- **Encode port category (`LogOS.LT.LOG.EncodePort2Cat.WithPort`)**: kernels equipped with an `EncodePort`.
  - engineering reading: compilation/synthesis is a port; encode coherence is an adapter obligation
  - capability-first projection pattern: use `PortStack.baseObj` with `LogOS.LT.LOG.EncodePort2Cat.stack` for the underlying kernel,
    and `PortStack.getObj LogOS.LT.LOG.EncodePort2Cat.port` for the encode payload.
- **Budget port (`LogOS/Ports/Universality/Budget.agda`)**: an explicit numeric/telemetry interface for code.
  - `BudgetPort`: a `View` from code into a chosen budget boundary preorder
  - `BudgetTransport`: an explicit adapter obligation relating the source/target budget readouts along `mapCode`
- **Budget-equipped kernels (`LOGᴳʳᵇ` / `LOGᵇ`)**: kernels equipped with a budget bus.
  - displayed layer over `LOG`, reindexed to the stronger `LOGᴳʳ` basis; `LOGᵇ` remains the observational option
  - implementations: `LogOS/Ports/Universality/ArchitectureBudgetBus2Cat.agda` (default internal basis), `LogOS/Ports/Universality/BudgetBus2Cat.agda` (observational)
  - capability-first projection pattern: use `PortStack.baseObj` with `...BudgetBus2Cat*.stack` for the underlying kernel,
    and `PortStack.getObj ...BudgetBus2Cat*.port` for the budget port payload.
- **QAdapter / valuation bus (`LogOS/Ports/Valuation/QAdapter.agda`)**: an optional quantitative parameter (scale algebra) that can be threaded
  through architectures via the budget port, without changing the kernel core.
  - chosen time presentation (explicit choice): `QClock Q` (time monoid + `τ : Time → Scale` + laws)
  - induced boundaries: `LogOS/Ports/Valuation/ScaleBoundary.agda`
  - Q-specialised bus: `LogOS/Ports/Valuation/QAdapterBus.agda` (`LOGQ`, `QKernel`, `kernel` / `port`, API projection names `qKernelOf` / `qPortOf`)
  - time-graded transport algebra: `LogOS/Ports/Valuation/QAdapterBudgetTransport.agda` (`QTimeBudgetTransport`, `traceBudget≤`)
  - time-graded bus (2-cat): `LogOS/Ports/Valuation/QAdapterBudgetTransport2Cat.agda` (`LOGQᵗ`, `TimeBudgetKernel`, `kernel` / `port`, API projection names `timeBudgetKernelOf` / `timeBudgetPortOf`)
- **Evaluator reflection (closure universal property)**: “maximal safe reflection” for readouts.
  - given a closure `N` and an evaluator `T`, the reflected evaluator is `T ∘ N`
  - it is the least `N`-stable evaluator above `T` (mechanised in `LogOS/LT/Theorems/EvaluatorReflection.agda`)
- **I/O port (`LogOS/Ports/IO.agda`)**: an *input-indexed telemetry surface*.
  - `admissible`: which inputs/tests are allowed at the interface boundary
  - `outputObs : I → View X O`: per-input output/telemetry probe into a chosen observation spec `O`
- **I/O adequacy (`LogOS/Ports/IO.agda`)**: an *interface completeness* principle:
  admissible I/O indistinguishability reflects refinement of output specs.

- **Restricted product / “almost everywhere” law (`LogOS/Ports/RestrictedProduct.agda`)**:
  boundary-wide finiteness/cofiniteness constraints packaged as an explicit, compositional law layer on dependent families.
  - `AlmostAll P` = “there is a finite (list-indexed) bad set outside of which `P` holds”
  - `Restricted Good F` = “a boundary family `F` is good outside finitely many indices”
  - `AEPreserves Good f` = “a pointwise map preserves goodness outside finitely many indices”
  - downstream packs can wrap their own transport notions with an `AEPreserves`
    proof and derive restricted-transport lemmas without changing the kernel core.

## Naming discipline (Context vs Index)

LogOS uses **context** as the default *approximation reading* of “an index for a family of refinement relations”.

Design rule (presentation only; no extra axioms):

- use the binder name `Context` in theorem surfaces that are intended to be read as “approximation regime”
  (budget/time/scale/observables), e.g. `ContextApproximation`, `ContextualStabilityTheorem`,
  and context-facing indexed constructions like `IndexedCenteredQuote` in `LogOS/LT/Theorems/CenteringQuote.agda`;
- keep the neutral name `Index` in fully generic spines (e.g. `IndexedConPreorder`) and in *structural indexing*
  (covers, components, positions) where “context” would be misleading.

Pedantry note:

- `Context` does **not** implicitly mean there is a weakening order on contexts.
  If weakening is part of the story, it is an explicit parameter (e.g. `_≤Ctx_` in `BoundaryGauge`).

## Remarks (semantics choices)

- **Granularity of modalities:** “locality”/“causality” are relative to a boundary choice (`I`, `O`) and a doctrine choice (e.g. `Flow`).
  If you relate different granularities, do so via explicit translations/ports (coarse-graining), not silent re-interpretation.
  See: `docs/Patterns/HowTo/HowTo_Build_Logic_Transformer_Architecture.lagda.md`.
- **Observation geometry (locales/nuclei reading):** a useful mental model is “boundaries as locales” and `Flow` as a nucleus-style closure
  selecting stable/effective specs, with contracts/institutions giving the model-theoretic bridge.
  - see: `docs/Patterns/Boundaries_As_AbstractLocales.lagda.md`

## Presentation dependence (why “many definitions” collapse)

The core stance is that **interface observation determines refinement**:

- the canonical code preorder is induced by pulling back `⊑` along `decode`;
- morphism refinement is pointwise after boundary observation (base `LOG`: `_⇒∂_`; realiser-first `_⇒_` is an equivalent view);
- any alternative “implementation relation” is valid only insofar as it is monotone w.r.t. the chosen probe(s).

This is made explicit in `LogOS/LT/Presentation.agda`.

Design reading (not a kernel theorem statement): **many “architecture choices” collapse** to the choice of
observables.
Once you commit to a view/probe suite, the coarsest admissible refinement relation compatible with that observation
is forced (pullback/initiality), so you do not get to separately choose an unrelated “implementation relation”.

Mechanised anchors:

- forcedness/minimality by observation (1D): `Presentation.toCanonical` and `SuiteForced` / `SuiteForcedᵈ`
  (`LogOS/LT/Presentation/ObservationInitiality.agda`).
- 2D analogue (homwise observation-induced shadows): `ShadowForcedByView`
  (`LogOS/Apps/LogicArchitecture/MetaTheory/Basis/ShadowInitiality.agda`).

Possible use (interpretation): treat “context = chosen observables, ordered by weakening” as the knob for
approximation/learning: start with weak observables, and add probes only when needed (see
`docs/Core/MetaTheory/Observation_Controlled_Approximation.lagda.md`).

## Weak-refinement guardrail (avoid collapse)

This repository intentionally stays **weak**:

- `⊑` is a preorder, not a partial order (no antisymmetry is assumed).
- `≼` is only a presentation alias for the same preorder relation; it is not a new semantics.
- `≈` is mutual refinement and must not be treated as equality.
- `≡` is used only for strict coherence/bookkeeping (S-tier), never as the primary comparison notion.

Engineering consequence: adding a port layer must not change what counts as refinement between adapters.
`DisplayedThin2Cat` enforces this by inheriting 2-cells solely from the base.
(In `Thin2Cat`, “2-cells” are literally refinement proofs in the hom-preorders; see `Thin2Cat₂Cells` in
`LogOS/LT/Thin2Cat.agda`.)

## Analogy pointers (non-binding) {#analogy-pointers-non-binding}

- **Cone theorem analogy**: a family of probes (a “cone of views”) determines the observable preorder as the
  intersection of their pullbacks.
- **Minimal model program analogy**: normalisation/flow can be read as iterated stabilisation toward a “minimal” boundary theory,
  while keeping interface semantics explicit and compositional.
- **μ-calculus analogy**: closure operators + stable points + quotation/evaluation (`quot`/`evalm`) are the order-theoretic core of recursive
  specification and partial self reference.
