<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# How to Build a Logic-Transformer Architecture

This guide is written for AI-assisted implementation in this repository.

Practical companion:
`docs/Patterns/HowTo/HowTo_Practical_Architecture_Tips.lagda.md`.

If you remember one thing: **interfaces are directed**.
An interface is a preorder of constraints plus a named observation function into it.
Everything else is derived: code order, adapter comparison, port composition, and “architecture”.

Design reading (not a new axiom): software architecture is about making choices, but you may need less choices than
people think.
In LogOS this is made precise by the forcedness/minimality theorems: once a `View` (or probe suite) is fixed, the
coarsest admissible refinement respecting that observation is forced (pullback refinement).
See: `LogOS/LT/Presentation.agda`, `LogOS/LT/Presentation/ObservationInitiality.agda`, and the 2D companion note
`docs/Core/MetaTheory/Observation_Controlled_Approximation.lagda.md`.

The capstone packaged version of that story is:

- `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`

Use it as the final regression target for LT architecture work. If a new layer
really follows the repository discipline, it should fit the same theorem shape:
observation-forced refinement, boundary-first factorisation, displayed
structure, Σ-totalisation, and explicit late strictification only where needed.

Practical distinction:

- build a new layer only when the lower-rung machinery is genuinely missing;
- otherwise reuse an existing layer and let the app specialize it honestly.
- when in doubt, start from one canonical lower-rung object and only add app-side packaging after it proves too small.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.HowTo.HowTo_Build_Logic_Transformer_Architecture where

-- Sync guard: public docs should prefer the curated API surface.
open import LogOS.API.LT
```

## Goals (architecture invariants)

- **Directed interfaces:** every interface is a preorder + a named observation (`View`), with monotone transport.
- **Coherence:** every new layer states coherences explicitly (refinement-first `⊑`/`≈` by default; strict `≡` only via explicit strictification ports).
- **Modularity:** keep kernel/ports/adapters/apps/API separated; compose by ports and stacks, not by cross-imports.
- **Auditability:** assumptions are parameters/records; avoid “ambient” axioms; stay `--safe`.
- **Refactorability:** refactors are always an option; prefer refactoring to breaking the layering or view discipline.

## Standardisation rules (reduce bespoke glue)

These are “boring” mechanical rules that keep the repository coherent and cut down boilerplate.

- **Stack → kernel morphisms:** author maps out of `stackKernel` as `StackMapLike`/`StackMap` and convert via
  `toKernelHom` (`LogOS/LT/Stack/Core.agda`). Avoid duplicating the same case split for `mapCode` and `decode-mapCode`.
- **ZF primitive constructor stack:** use the canonical constructor stack definition
  `LogOS/Apps/ZFC/Stack/ZFCore/PrimitiveStack.agda` (and re-export it if you need the names), rather than re-defining
  `PrimOp`/`PrimCode`/`primView`/`primStack` in multiple places.
- **Law decorations:** when you decorate a base category with a “witness”/law layer and then Σ-totalise, prefer the
  port authoring templates (`LogOS/LT/Ports/Template/Singleton2Cat.agda`,
  `LogOS/LT/Ports/Template/LawSingleton2Cat.agda`) over bespoke `LawDisplayedOn`/`DecoratedThin2Cat` glue.

## Staged admissibility + reification (ZFC pattern, now core)

If an architecture needs a “reify constraints/predicates as points” step, treat it as an **optional port layer** and
keep it **restricted-by-default**.

Core interfaces (reusable types):

- `LogOS/Ports/Reification/Admissible.agda` (`RestrictedReification`, `TotalReification`, `decode-reify-stable≈`)
- `LogOS/Ports/Reification/Staged.agda` (`StagedReification` + conversions; staged admissibility is the primitive ledger)
- `LogOS/Ports/Reification/CrossStage.agda` (successor-stage predicate reification as a pure bridge)

ZFC instance modules (specialisations + discipline checks):

- `LogOS/Apps/ZFC/Stack/AsymptoticReification/ReificationPort.agda`
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/StagedAdmissibility.agda`
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/CrossStageReificationPort.agda`

Do:

- keep reification restricted; supply explicit admissibility (`Reifiable` / `ReifiableAt`)
- stage-index admissibility when you want late-collapse discipline; derive the restricted surface by forgetting stages
- keep strong assumptions as explicit upgrade records/ledgers (see ZFC towers), not as ambient global bundles

Don’t:

- combine total reification with `Flow = id` on a same-stage predicate boundary without an explicit quarantine layer
  (Russell-style diagonalisation risk)

## Prism mode: strict transformer-first target

Use this stricter profile for all universality code in this directory:

- **No hidden contracts:** every transport between paradigms must be a named port record or a named morphism lemma.
- **Relation stance enforced:** default adapter coherence is `≈` (behavioural); equality-bearing witnesses belong only in explicit `Strictification` / `Definitional` lanes (for example `LogOS.API.Strictification.Kernel` via `Ports.ClassicalLimit`).
- **One-way flow direction:** `Ports -> Adapters -> Apps -> API`; never reverse this edge for new universality features.
- **No “macro without kernel”:** any reusable stack language must be a `Stack` object first, with composition surfaced as a kernel only if needed.
- **Refactor by default:** whenever a theorem or adapter accumulates more than one obligation, split obligations into a port/ledger shape and surface a clean deck.

In prism mode, stop immediately if a module:

- adds a semantic relation that is not induced by a `View`,
- adds assumptions as local variables without a named assumption port,
- mixes strict and lax obligations in the same lemma.
The refactor rule is always on: if a check shows a conceptual mismatch, stop adding new interfaces and refactor the layer boundaries first.

## Implementation recipe (start here)

When implementing a new subsystem, follow this exact order. It matches the repo's checks and keeps the "transformer picture" intact.

1. Pick the **layer** and file location (see `docs/Core/Architecture/Diagram.lagda.md`; enforced by `scripts/check/layer_order_check.sh`).
2. Name the boundary constraints (a `ConPreorder`).
3. Name the observation (a `View`), and pull back relations along it (`PullbackPreorder`, `_⊑[_]_`).
4. Package code as a `Kernel` only when you truly need a code type; use the induced order (`CodePreorder`).
5. Implement adapters as `KernelHom` and keep semantics preservation refinement-first (`decode-mapCode : ≈`).
6. Choose port shape (view-only, input-indexed probes, or displayed structure over an explicit base thin 2-category; see "Port shapes" below).
7. Keep assumptions explicit: define the semantics ledger and the realisation family,
   then reuse the canonical architecture surface for the derived apex and
   denotations.
   Example (dependent-first): `LogOS/Ports/Realisations/Architecture.agda`.
8. Wire policy hooks:
   - New `LogOS/LT/**`: add exactly one `-- SpecRef:` line and import the module from `docs/Core/Spec/LogicalTransformers.lagda.md` (`scripts/check/spec_ref_check.sh`).
   - New `LogOS/LT/Theorems/**`: surface it via `LogOS/API/Theorems/Core.agda` or `LogOS/API/Theorems/Strictification.agda` (`scripts/check/theorems_catalog_check.sh`).
   - New non-Host core modules: ensure they are reachable from `LogOS/API/LT.agda` or the spec docs (`scripts/check/reachability_check.sh`).
   - If your change affects the LT architectural spine, check that it still
     fits `ObservationPreservingArchitecturalNormalForm` instead of introducing
     a bespoke parallel story.
9. Use `make check` only as a very fast smoke test; use the standard lanes
   `make check-policy`, `make check-core`, `make check-integration`,
   `make check-docs`, and `make check-lib` while iterating; run
   `make check-all` for AI-assisted hand-off and for the cold umbrella gate.
   Use `make check-all-warm` when you want the same full lane without a clean.

## Basis choice (LOG vs LOGᴳ)

LogOS supports two basis choices for port stacks and LT categories. Both are first-class and explicit:

- **LOGᴳ basis (default for boundary-only architecture):** use `LOGᴳ` directly when your law only needs
  boundary transport/refinement, and use `LOGᴳʳ…` only when you also need implementation witnesses.
  Typical examples:
  `LogOS.LT.LOG.ArchitectureFlowContract2Cat.WithPort`,
  `LogOS.LT.LOG.ArchitectureBulkBoundary2Cat.WithPort`,
  `LOGᴳʳᶠ`,
  `LOGᴳʳ∂`,
  `LogOS.Ports.Universality.ArchitectureBudgetBus2Cat.WithPort`.
- **LOG basis (observational/app-facing):** the observational basis, appropriate for physics/Deutsch-facing apps
  and for contexts where boundary strength should remain purely observational
  (e.g. `LogOS.LT.LOG.Flow2Cat.WithPort`, `LogOS.LT.LOG.Contract2Cat.WithPort`, `LogOS.LT.LOG.EncodePort2Cat.WithPort`,
  and the quote law-port `LogOS.LT.LOG.QuotePort2Cat.WithPort`).

Curated API surfaces:

- `LogOS/API/Ports/LTDecorations.agda` defaults to LOGᴳ-basis exports.
- `LogOS/API/Ports/LTDecorationsLOG.agda` exposes the LOG-basis explicitly.

Conservative rollout pattern:

1. Start an app or port stack on LOG.
2. Add LOGᴳ ports alongside (same boundary, stricter internal refinement).
3. Use weakening functors (`forget…` / `…→LOG`) to expose LOG views for apps.
4. Strengthen modules one by one while preserving applications.

This pattern lets you iterate from approximated/verified computing toward stricter modules, while keeping the
LOG-basis observational interface stable.

## Transformer picture (cheat sheet)

For the full tower and placement policy, use
`docs/Patterns/Content_Placement.lagda.md`; the summary below is only the
implementation mnemonic.

The core picture is a pipeline from *observation* to *composition*:

```text
ConPreorder (boundary constraints)
  ^ View μ (named observation)
Code --decode--> Con boundary
Kernel        = boundary + Code + decode
KernelHom     = Σ BoundaryHom (BoundaryImplementation approx)
             = map∂ + implementCode + decode-implementsBoundary (≈ coherence)
LOG           = kernels/adapters with 2-cells (⇒∂) by boundary-driven observational refinement
Displayed port= extra admissibility/coherence over LOG (then totalise)
Stack         = family of Views into a shared boundary, reified as kernels + macro/program kernel
Ledger -> Deck-> explicit assumptions (inputs) -> derived transformer package (surface)
```

Meta-theory pointer (architecture justification): `docs/Core/MetaTheory/Observation_Controlled_Approximation.lagda.md`
spells out the “observation-controlled approximation” stance behind using thin 2-categories (`Thin2Cat`) as the
consumed wiring interface (contexts = observables; adding observables refines approximation; forgetting observables
is functorial).

The theorem bundle `architecturalNormalForm` is the code-level capstone of that
reading: it packages observation-controlled approximation, boundary-first
factorisation, displayed totalisation, and explicit strictification into one
public theorem surface.

## Shared distributed semantics transformers

When your target is physics-inspired PL modelling (especially concurrency/effects), use the **shared, distributed**
semantics discipline:

The generic shared-boundary / many-realisations surface now lives in:

- `LogOS/Ports/Realisations/DependentStack.agda`

Downstream packs should specialise that generic surface rather than defining a
separate primitive architecture.

Prerequisites (chosen once per semantics; an explicit modelling choice):

1. a locality index type `I` (regions / observers / subsystems),
2. a local observation family `O : I → ConPreorder`,
3. a local causal doctrine family `GC₀ : (i : I) → GuardedClosure (O i)` (“the law” at each region).

Then treat your systems as living over the **shared boundary** `LocalBoundary I O = DFunPreorder I O` with the
**shared closure** `pointwiseClosure GC₀`. This makes combined meaning literally a tuple of local readouts, and makes
causality the single transported closure law (Flow preservation) rather than a global axiom.

Uniform special case (inline constant-family specialisation):

- choose `O = λ _ → O₀` and `GC₀ = λ _ → GC₀₀`, recovering
  `LocalBoundary I O₀ = FunPreorder I O₀` with `pointwiseClosure GC₀₀`.

Global coherence is optional (explicit strictification):

- Most correspondences over function-shaped boundaries are proven **pointwise** (`∀ i → …`).
- Upgrading pointwise equality into strict function equality is packaged as an explicit assumption port
  `Globalise I X` in `LogOS/Ports/Globalise.agda`.
- Use this only when you genuinely need strict global equality rather than
  pointwise refinement/equivalence.

Boundary-wide (non-pointwise) constraints are also optional (“don’t collapse to strict global coherence early”):

- Treat almost-everywhere / finiteness / coherence conditions as an additional boundary-wide closure or contract on the
  shared boundary, and apply it as a final unrolling step.
- For list-indexed “finite bad set” (restricted product / a.e. conditions), see
  `LogOS/Ports/RestrictedProduct.agda`.
- Mechanically this is iterated effectivisation:
  `decodeᵉᶠᶠ² = Flow GC₁ (Flow GC (decode γ))` where `GC₁` is an additional closure on the shared boundary
  (see `LogOS/LT/Theorems/Effectivisation.agda`, `decode-effectiveKernel²`).

Caveat: this discipline enforces exactly the causal/normalisation notion you encode as `GC₀`/`Flow`;
it becomes useful once `GC₀` is chosen to capture the concurrency/resource invariants you care about.

Distinction to keep straight:

- the LT core supports **per-system** closures (`LogOS.LT.LOG.Flow2Cat.WithPort`) in full generality;
- a shared distributed-semantics transformer is the **shared** subworld you get after fixing `(I, O, GC₀)` and keeping translations explicit
  (the repository term “physical transformer” refers to this pattern).

Micro vs effective: `I`, `O`, and `GC₀` can be *microscopic* (fine-grained) or *effective* (coarse-grained).
Keep the distinction explicit; “effective locality/causality” is typically implemented by an explicit coarse-graining
translation/port between boundaries, not by silently changing what the indices mean.

Observation geometry reading (optional): treat `Opp (DFunPreorder I O)` as a locale of “opens” and `Flow` as a nucleus-style closure;
stable points are the effective opens. See `docs/Patterns/Boundaries_As_AbstractLocales.lagda.md`.

Design note + anchors: `docs/Patterns/Shared_Distributed_Semantics.lagda.md`, `LogOS/Ports/PhysicalSemantics/Core.agda`,
`LogOS/Ports/Locality/Core.agda`, `LogOS/Ports/PhysicalTransformers.agda`,
`LogOS/Ports/Realisations/DependentStack.agda`.

Concrete examples in v1.1:

- concurrency boundary + causal closure: `LogOS/Apps/Concurrency/HappensBefore.agda`

Practical downstream companion
------------------------------

For “what should I actually do when the lower-rung machinery already exists?”,
see:

- `docs/Patterns/HowTo/HowTo_Practical_Architecture_Tips.lagda.md`
- flagship stacked-transformer universality deck:
  `LogOS/Apps/Universality/Architecture.agda`
- universality ledger (assumption-scoped):
  `LogOS/Ports/Universality/CTD/Ledger.agda` and `LogOS/Apps/Universality/CTD.agda`

## The three governing equations

These three equations (one definition, one equality, one inequality) are the reason this repo scales.

### 1) Code order is induced by observation

The code preorder is not a separate design choice: it is the pullback preorder along `decode`:

```text
γ ≼Code δ  :⇔  decode γ ≼Bnd decode δ
```

This is implemented as `CodePreorder` in `LogOS/LT/Kernel.agda`.
Concretely, it is definitional pullback:

```agda
codePreorder-def
  : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode)
  → CodePreorder K ≡ PullbackPreorder (forget (decodeView K))
codePreorder-def K = refl

codeOrder-by-decode
  : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) (γ δ : Code K)
  → (γ ⊑[ forget (decodeView K) ] δ) ≡ _⊑_ (bnd K) (decode K γ) (decode K δ)
codeOrder-by-decode K γ δ = refl
```

**PL reading:** don’t argue about programs directly; argue about what they *mean at the boundary*.
If you can’t name the observation, you don’t get a new order.

### 2) Adapters preserve boundary semantics by ≈-coherence

A `KernelHom K K'` does not get to invent semantics: it must commute with observation up to mutual refinement:

```text
decode K' (mapCode h γ) ≈ map∂ h (decode K γ)
```

This is `decode-mapCode` in `LogOS/LT/Hom.agda`.

```agda
decode-mapCode-law
  : ∀ {ℓ ℓRel ℓCode} {K K' : Kernel ℓ ℓRel ℓCode}
  → (h : KernelHom K K')
  → (γ : Code K)
  → _≈_ (bnd K') (decode K' (mapCode h γ)) (map∂ h (decode K γ))
decode-mapCode-law h γ = decode-mapCode h γ
```

**Engineering reading:** adapters are wiring harnesses that preserve meaning at the boundary by construction,
not by convention.

Boundary transparency (“adapters are pure wiring”): when you intend an adapter to *not* change boundary constraints
at all, make that an explicit assumption/port instead of a convention. Use:

- `LogOS/Ports/BoundaryTransparency.agda` (`BoundaryTransparent`)

### 3) Nontrivial structure is expressed as lax coherence, not hidden axioms

When you need extra structure, add it as *explicit data + explicit obligations*.
Crucially, coherence is usually **lax** (an inequality), not strict equality.

Canonical example (Flow preservation) from `LogOS/LT/HomFlow.agda`:

```text
map∂ (Flow c) ≼ Flow (map∂ c)
```

This one refinement step is the key engineering lemma: it makes “normalisation/stabilisation”
transport across translations without collapsing refinement into equality.

Tooling loop (key theorem):

- if `h` is flow-preserving, then translating *commutes with normalisation up to refinement*:
  `map∂ h (Flow (decode γ)) ≼ Flow (decode (mapCode h γ))`.
- Code anchor: `LogOS/LT/Theorems/Effectivisation.agda` (`normalize-decode-mapCode`).
- Unrolling packaging: treat `Flow` as a kernel refinement `decodeᵉᶠᶠ = Flow ∘ decode` (code unchanged),
  so the loop is literally “lax commutation for reflected observation”. Code anchor: `LogOS/LT/Theorems/Effectivisation.agda` (`effectiveKernel`).
- Effective-semantics reading: define `effObs ≔ Flow ∘ decode`; then “packet equivalence” is the pullback
  equivalence along `effObs` (see `LogOS/LT/Theorems/EffectivePackets.agda`).
- Guarded self-reference: if you also choose an `EncodePort` satisfying `decode ∘ encode ≈ Flow`, you get a `QuotePort`
  (safe “partial self-reference”; see `LogOS/LT/LOG/QuotePort2Cat.agda`).
  ZFC pack note: the corresponding equivalence is stated for the explicit *total/unrestricted* wrapper
  (`TotalPredicateReification`), not for the restricted-by-default predicate reification ledger.
- Reification packaging: `Flow` + `QuotePort` + an explicit reification ledger
  yields guarded self-reference and stable-constraint reification. Code anchors:
  `LogOS/Ports/Reification.agda`, `LogOS/LT/LOG/QuotePort2Cat.agda`.

### Optional: σ-directed completeness for iteration summaries

If you want a single “total run summary” boundary constraint (or a least fixed point spine), keep the kernel weak and
add explicit completeness structure on the boundary:

- finite joins + bottom: `FinSup` (`⊥ᶠ`, `_⊔ᶠ_`)
- σ-directed ω-suprema: `SigmaDCPO` (`supσ`, `ubσ`, `leastσ`)
- derived ω-sup for arbitrary sequences: `supω` (prefix-join chain construction)

This is implemented in `LogOS/LT/Sup/` and used by the optional `run` combinator in `LogOS/LT/Iteration.agda`.
Reader-facing dictionary: `docs/Interpretations/Views/Mathematics_And_Completion.lagda.md`.

```agda
flow-preservation-law
  : ∀ {ℓ ℓRel ℓCode} {K K' : Kernel ℓ ℓRel ℓCode}
  → (GC : GuardedClosure (bnd K))
  → (GC' : GuardedClosure (bnd K'))
  → (h : KernelHom K K')
  → KernelHomFlow GC GC' h
  → (c : Con (bnd K))
  → _⊑_ (bnd K') (map∂ h (Flow GC c)) (Flow GC' (map∂ h c))
flow-preservation-law _ _ _ HF c = preserves-Flow HF c
```

### Corollary: adapters form a thin 2-category via observational refinement

Between adapters `f g : K → K'`, the 2-cell (refinement) is defined by *boundary observation*.
There are two canonical, equivalent presentations:

```text
f ⇒∂ g  :⇔  ∀ γ,  map∂ f (decode γ) ≼Bnd map∂ g (decode γ)

f ⇒ g   :⇔  ∀ γ,  decode (mapCode f γ) ≼Bnd decode (mapCode g γ)
```

The `decode-mapCode : ≈` coherence carried by every `KernelHom` makes these two refinements equivalent.

In code, `LOG` uses `_⇒∂_` as its 2-cells (pullback along `transportView`) so that refinement is definitionally
insensitive to the chosen implementation map (`mapCode`). The implementation-first refinement `_⇒_` remains available only as an
explicit derived view under `ImplementationView`; convert via `⇒↔⇒∂` in `LogOS/LT/Hom.agda`.

```agda
refinement∂-def
  : ∀ {ℓ ℓRel ℓCode} {K K' : Kernel ℓ ℓRel ℓCode}
  → (f g : KernelHom K K')
  → (f ⇒∂ g) ≡ (f ⊑[ forget (transportView {K = K} {K' = K'}) ] g)
refinement∂-def f g = refl
```

**Engineering reading:** adapters are comparable by what they preserve/strengthen in observable semantics,
not by internal representation tricks.

## Layer model (hexagonal + separation of concerns)

The repository enforces a strict separation-of-concerns story. Keep it.
Layering is enforced by `scripts/check/layer_order_check.sh` using the canonical order
in `scripts/lib/layers.sh` (rendered in `docs/Generated/Architecture_Layer_Order.md` and `docs/Core/Architecture/Diagram.lagda.md`).

1. **Kernel** (`LogOS/LT/Kernel.agda`, `LogOS/LT/Hom.agda`, `LogOS/LT/LOG/Kernel2Cat.agda`)
   - `Kernel`: boundary constraints `bnd`, code `Code`, observation `decode`.
   - `KernelHom`: transports boundary + code with ≈-coherence; equality-based variants live only under `LogOS.API.Strictification.Kernel`.
   - `LOG`: a thin 2-category of components/adapters with boundary-driven observational 2-cells (`_⇒∂_`).

2. **Ports** (`LogOS/Ports/`, plus displayed ports under `LogOS/LT/`)
   - Ports are *interfaces*: they name what can be observed and which obligations matter.
   - If arrows need extra obligations, represent the port as displayed structure over the chosen base thin 2-category.
   - Displayed ports live under `LogOS/LT/**` so they can talk about `LOG` without creating import cycles;
     `LogOS/Ports/**` is the user-facing wrapper layer.

3. **Adapters** (`LogOS/Adapters/All.agda`, plus concrete adapter modules)
   - Adapters implement ports. They may import ports. Ports must not import adapters.

4. **Apps** (`LogOS/Apps/`)
   - Apps compose ports and adapters into usable stacks, surfaces, and proofs.
   - Example: `LogOS/Apps/Opacity/Demo.agda`.

5. **API** (`LogOS/API/`)
   - Curated, stable exports (used by docs and downstream code).
- Prefer surfacing through `LogOS/API/LT.agda` / `LogOS/API/Ports.agda`.

**The architectural payoff:** you can add new behavior by adding new ports/adapters/apps without touching
the kernel, and the logic of “what is preserved” remains first-class.

## Ledgers and decks (make assumptions explicit)

This repo stays modular by making assumption boundaries first-class.

- A **ledger** is a record of explicit assumptions (inputs) needed to build a subsystem.
- A **deck** is the derived "transformer picture" packaged for downstream use: kernels, per-operation kernels,
  injections, and any transport lemmas between equivalent presentations.

Concrete example pattern:

- `LogOS/Apps/ZFC/Stack/AsymptoticReification.agda`: ledger-style assumptions
  (a reification doctrine `PredicateReification` which is admissibility-gated by an explicit `Reifiable` family,
  plus explicit stability records; a separate opt-in `TotalPredicateReification` wrapper exists for experiments).
- `LogOS/Apps/ZFC/Stack/ReifiedTower.agda`: curated ledger packaging
  (bundle reification+stability with explicit ω/Infinity/Foundation/Choice into `ZFCStackFO`).
- `LogOS/Apps/ZFC/Stack/ProfileTower/Core.agda`: the constructor-layer view that reifies the primitive constructors as a
  `LogOS.LT.Stack` and exposes the "inject each primitive operation into the stack kernel" picture directly, without an extra façade wrapper.

## Directed interfaces (the definition that matters)

In this repository, a “directed interface” is not a bag of functions.
It is a **directional semantics interface** with three mandatory ingredients:

1. **A constraint carrier**: a `ConPreorder` whose order `⊑` (public-facing alias `≼`) is the interface’s truth/refinement notion.
2. **A named observation**: a `View` into that carrier (or a family of views indexed by inputs).
3. **Transport**: monotone maps induced by translations/adapters, with explicit (often lax) coherences.

Everything else is derived:

- relations on your data are pullbacks along the observation (`View` discipline),
- adequacy claims are “reflection” properties from entailment back to refinement,
- compositionality is functoriality (strict or lax, but never implicit).

### Relation stance (strict / refinement / guarded)

Use the core relation stance consistently:

- **S-tier (`≡`)**: only for strict coherence/bookkeeping as an explicit, opt-in check (e.g. strictifying `decode-mapCode` to propositional equality via `Ports.ClassicalLimit` or strictifying whole port stacks via `PortStack.ClassicalLimit`).
- **G-tier (`⊑` / public-facing alias `≼`, plus `≈`)**: behavioral comparison; this is where your interface lives.
- **H-tier (guarded)**: assumption-scoped judgments; keep them explicit as parameters/records.

This is the strict/refinement/guarded reading from the core spec, not the
separate shape/guard/realiser overlay used by the bi-pyramid architecture view.

If you’re tempted to state a behavioral law using `≡`, you probably want `⊑` / `≼` (or `≈`) instead.

## Port shapes (choose deliberately)

Most design mistakes in this repo are “wrong port shape”.

### A) Plain observation port (View-only)

If the port is “what can be observed”, it should often be a `View` plus pullback relations.

- Example: `LogOS/Ports/Opacity.agda` (`OpacityPort`).

**Consequence:** the refinement/equivalence theory is induced by pullback (no new axioms; no bespoke relations).

### B) Input-indexed port (tests/probes as first-class)

If what you can observe depends on inputs (queries, environments, prompts, test cases),
make that dependence explicit as an indexed family of views.

- Example: `LogOS/Ports/IO.agda` (`IOPort`), which packages a `ProbeSuite` and defines adequacy as reflection.

**PL reading:** admissible inputs are an interface boundary; adequacy is precisely “my interface is strong enough”.

### C) Displayed port over an explicit base (object + arrow structure)

If objects and arrows need extra structure/obligations, model the port as displayed structure over an explicit base
thin 2-category and totalise it.

- Core construction: `LogOS/LT/DisplayedThin2Cat.agda` (`DisplayedThin2Cat`, `DecoratedThin2Cat`, `ProductDisplayed`).
- Contract port: `LogOS/LT/LOG/Contract2Cat.agda` (objects `mkContract K c`, morphisms require `c' ≼ map∂ h c`).
- Flow port: `LogOS/LT/LOG/Flow2Cat.agda` (objects choose a closure, morphisms satisfy Flow-naturality).

For internal architecture-first ports, use `LOGᴳʳ` as the default base and
reindex LOG-basis ports explicitly when needed.

**Note:** 2-cells remain observational refinements on the underlying adapters.
So adding ports doesn’t change the meaning of refinement; it changes what objects/morphisms *are allowed* to be.

### D) Numeric bus (Budget / QAdapter)

If you want the transformer picture to speak about **numerics** explicitly (cost, fuel, time, grades),
do not bake valuation algebra into `Kernel`. Instead: make numerics a first-class boundary interface and
transport them explicitly as a displayed port.

The pattern:

1. Choose a numeric boundary preorder `Budget : ConPreorder … …`.
2. Equip each kernel `K` with a `BudgetPort (Code K) Budget` (a `View` measuring code into the budget boundary).
3. Equip each translation `h : KernelHom K K'` with a `BudgetTransport` obligation.
4. Totalise to get the thin 2-category `LOGᴳʳᵇ Budget` (kernels-with-budget-bus).
   Use `LOGᵇ Budget` when you want a purely observational basis.

This is implemented as a displayed layer over `LOG` and reindexed to `LOGᴳʳ`:

- `LogOS/Ports/Universality/ArchitectureBudgetBus2Cat.agda` (`LOGᴳʳᵇ`, default internal basis)
- `LogOS/Ports/Universality/BudgetBus2Cat.agda` (`LOGᵇ`, observational option)

The flagship downstream consumer is now the universality architecture façade:

- `LogOS/Apps/Universality/Architecture.agda`

It packages one adapter stack, one CTD ledger, one measured-agreement family,
and both `Flow + Budget` stack bases without rederiving app-local transport
machinery.

**Direction note:** the transport law is stated in the boundary preorder you choose.
If you want “translations do not increase cost” but your cost order is the usual `≤`, use `Opp` (or pick the
boundary order accordingly) so that the law reads in the intended direction.

#### Specialisation: `QAdapter` as a bus

For a structured quantitative parameter, use `QAdapter` as an *optional bus*:
it fixes a **scale algebra** (grades/cost), and you can additionally choose a **clock/presentation**
`QClock Q` when you want to speak about time (a time monoid + `τ : Time → Scale` + laws).

- `QAdapter`: `LogOS/Ports/Valuation/QAdapter.agda`
- `ScaleBoundary Q : ConPreorder ℓQ ℓQ`: `LogOS/Ports/Valuation/ScaleBoundary.agda`
- `LOGQ Q = LOGᵇ (ScaleBoundary Q)`: `LogOS/Ports/Valuation/QAdapterBus.agda`
- refinement-first finite-join prequantale vocabulary: `LogOS/Ports/Valuation/AbstractJoinPrequantale.agda`
- quantic nuclei (closures coherent with valuation algebra): `LogOS/Ports/Valuation/AbstractQuanticNucleus.agda`
- generated closures by ω-iteration: `LogOS/LT/Sup/AbstractGeneratedClosure.agda`

One architectural consequence is that refinement between translations stays the same boundary-driven preorder
(base `LOGᴳʳ` internally, with a weakening to the observational `LOG` view when needed).
Numerics become explicit port data + explicit transport obligations.

```agda
-- A QAdapter induces a canonical budget boundary (its scale preorder).
qBudget : ∀ {ℓQ} → QAdapter ℓQ → ConPreorder ℓQ ℓQ
qBudget = QAdapterBus.QBudget

-- The budget-bus thin 2-category specialised to QAdapter.
LOGQ-example : ∀ {ℓ ℓRel ℓCode ℓQ} (Q : QAdapter ℓQ) → Thin2Cat _ _ _
LOGQ-example {ℓ} {ℓRel} {ℓCode} Q =
  QAdapterBus.LOGQ {ℓ = ℓ} {ℓRel = ℓRel} {ℓCode = ℓCode} Q
```

#### Algebraic strengthening: graded/time budget transport (Option 2)

`QAdapterBus` gives you a clean **bus shape** (a budget `View` plus monotone transport obligations).
If you want the transformer picture to be able to state and compose **quantitative bounds** (grades/time that
accumulate under composition), use:

- `LogOS/Ports/Valuation/QAdapterBudgetTransport.agda` (transport algebra)
- `LogOS/Ports/Valuation/QAdapterBudgetTransport2Cat.agda` (displayed/Σ-totalised packaging)

This module strengthens the transport obligation in two composable ways:

1. `QBudgetTransport`: a translation carries an explicit `grade : Scale`, with law
   `budget(mapCode h γ) ≤s budget(γ) · grade`.
2. `QTimeBudgetTransport`: relative to a chosen `QClock Q`, a translation carries an explicit `time : Time`,
   with law `budget(mapCode h γ) ≤s budget(γ) · τ time`.

Because `QAdapter` supplies the `·` algebra and the chosen clock supplies the `τ` laws (`τ-+`, `τ-zero`),
these transports compose cleanly.
Totalising the resulting displayed layer gives:

- `LOGQᵗ Q` (kernels equipped with a time-graded budget bus).
- `LOGQᵗ Q clock` (kernels equipped with a time-graded budget bus, relative to the chosen clock).

#### Concurrency and time (design options)

Time is not intrinsic to the kernel core; it only exists after you make an explicit **clock choice**
`clock : QClock Q` (a time monoid plus `τ : Time → Scale` into the shared scale algebra).

When you build multi-component models, you have a few clean options:

1. One shared clock:
   choose a single `clock : QClock Q` for the whole architecture.
   This makes time-labelled composition direct: everything lives in the same `LOGQᵗ Q clock`.

2. Concurrency-aware clock:
   still choose one shared `clock`, but pick its `Time` so it already *models concurrency* (for example a
   vector-clock-like monoid, or a trace/pomset-style time object).
   You keep the same composition story, but your “time” axis is no longer forced to be linear.

3. Multiple clocks plus explicit conversions:
   let different subsystems use different clocks `clockᵢ : QClock Q`, and add an explicit clock-change map
   when you compare or compose time labels across those subsystems.
   In this option there is intentionally no silent interoperability: time is presentation-dependent unless
   you supply a morphism that relates the presentations.

If you only need *numeric bounds* but do not want to commit to a time semantics, prefer the grade-only bus
(`QBudgetTransport` with `grade : Scale`), and treat “time” as a derived presentation via a chosen clock.

The same algebra lets you state iteration bounds for endomaps:

- `traceBudget≤` (an `n`-step budget bound for `traceCode`, using `timeIter` to accumulate time, relative to the chosen clock).

You can stack the numeric bus with other independent port layers using `ProductDisplayed`
(e.g. Flow + Budget + Contracts), then totalise once.

## Making it nontrivial (without losing modularity)

“Nontrivial” here means: the system uses directed structure and 2-categorical composition,
instead of being a thin wrapper around ordinary functions.

### Move 1: Use contracts as a first-class boundary object

Contracts reify “a component plus a chosen boundary constraint”.

- Satisfaction/contract-law vocabulary: `LogOS/LT/Contracts.agda`.
- Contract category: `LogOS/LT/LOG/Contract2Cat.agda`.

**Architecture reading:** a contract is a port instance pinned to a specific boundary requirement.
Composition becomes “does this adapter preserve/strengthen the contract?”.

### Move 2: Use closure (Flow) as a lax modality

Flow is a closure operator on boundary constraints: monotone, inflationary, lax-idempotent.

- Closure interface: `LogOS/LT/Flow.agda`.
- Functoriality requirement (lax coherence inequality): `LogOS/LT/HomFlow.agda`.
- Resulting thin 2-category: `LogOS/LT/LOG/Flow2Cat.agda`.

**PL reading:** Flow is a disciplined normaliser on specs; the lax law is the whole compositionality story.

### Move 3: Make a stack into a kernel (macros become code)

Stacks are how you get a programmable “language construction kit” without leaving the kernel discipline.

- Stack core (“stack-as-kernel”): `LogOS/LT/Stack/Core.agda`.
- Macro/program DSL (`ViewExpr`): `LogOS/LT/Stack/Program.agda` (surfaced by `LogOS/LT/Stack.agda`).

**PL reading:** you can build a typed macro language (`ViewExpr`) whose semantics is still `decode`.
This is how you get real programmability without inventing a second semantics layer.

### Move 4: Use partial reflection only via stable points

Reflection is allowed only when controlled by explicit closure structure.

- Reflection interface: `LogOS/LT/Reflection.agda`.
- KZ-style packaging: `LogOS/LT/AbstractKZ.agda` (Flow + stable points + `quot ⊣ evalm`).
- Code-level “quotation as a port”: `LogOS/LT/LOG/QuotePort2Cat.agda` (encode + flow + `decode ∘ encode ≈ Flow`).

**Safety reading:** reflection is a port/doctrine, not a meta-level excuse.

### Move 5: Compose ports by product of displayed structures

This is where “separation of concerns” becomes *algebraic*.
If two ports are independent, compose them with `ProductDisplayed` and totalise once.

- Generic product: `LogOS/LT/DisplayedThin2Cat.agda` (`ProductDisplayed`).
- Example composition: `LogOS/LT/LOG/ArchitectureFlowContract2Cat.agda` (Flow + Contract, LOGᴳ basis).

**Engineering reading:** weak coupling between ports; strong obligations inside each port; shared refinement notion.

### Move 6: Reuse the same totalisation step as a hierarchy generator

When the next layer is not just another static port but a **generated stage**, do not invent a second packaging style.
Reuse the same displayed-totalisation step explicitly:

- one-step stage packaging: `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`;
- generated closure/effectivity from explicit Kleene data: `LogOS/LT/Sup/AbstractGeneratedClosure.agda`, `LogOS/LT/Effectivity.agda`;
- closure-gated semantic cap: `LogOS/LT/Theorems/StableCompletion.agda`.

Use them in that order:

1. encode the admissible layer as displayed data over the current stage;
2. totalise once to obtain the next stage;
3. if you need an actual generated closure/effectivity doctrine, derive it explicitly from completeness/continuity data;
4. only then use stable completion, when the goal is the canonical stable semantic surface rather than stage generation itself.

This is the repository-level way to build cumulative hierarchies. It is also the right reading of the current ZFC base layer: stage generation is one thing, generated closure/effectivity is another, and stable completion is the semantic cap after a closure has been chosen.

If your stage is generated locally by filtering existing small generators before
you totalise, reuse:

- `LogOS/LT/Presentation/GeneratedSubobject/Core.agda`
- `LogOS/LT/Presentation/GeneratedImage.agda`

This is the presentation-side companion to `SuccessorStage`: it packages the
small generator-to-generated-object steps explicitly, so apps can reuse the
same local transformer pattern instead of open-coding filtered subobjects or
generator-indexed images.

If the semantic predicate you want to filter by is *not* itself small, keep
that boundary explicit as a `SmallClassifier` port rather than pretending the
carrier forced it. The current iterative-tree ZFC model uses exactly that move:
Replacement is generated directly, while Separation still needs a small
classifier witnessing that formula truth can be read at the child-index level.

If you want to eliminate that seam explicitly, move one stage up instead of
smuggling in same-stage comprehension. The reusable pattern is now:

- `LogOS/Apps/ZFC/Stack/AsymptoticReification/CrossStageReificationPort.agda`
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/CrossStageFOFromReification.agda`

The concrete iterative-tree example is:

- `LogOS/Apps/ZFC/Models/IterativeSetTree/SuccessorTruthLift.agda`
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/Hierarchy.agda`
- `LogOS/Apps/ZFC/Stack/AsymptoticReification/HierarchySlice.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/Hierarchy.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/CumulativeHierarchy.agda`
- `LogOS/Apps/ZFC/Models/IterativeSetTree/Semantics.agda`

Reading: formulas on stage `n` are not necessarily small classifiers on stage
`n`, but they *are* small classifiers on stage `n + 1`. If you want that move
to be the primary architecture rather than an isolated theorem, package it as a
cumulative hierarchy with an explicit typed split:

- one hierarchy section across stages,
- one canonical successor slice cut from that section,
- one canonical bridge inside the slice,
- same-stage proof models only after explicit local completion.

If you want a downstream-facing surface, add a narrow semantic entrypoint that
re-exports the stage-local assumptions, the hierarchy-section type, and the
slice constructor.

**Best practice (PortStack DSL):** for anything beyond a 2-port toy product, prefer the typed stack interface:

- Define tagged ports using `LogOS/LT/Ports/PortSig.agda` and `LogOS/LT/Ports/PortStack.agda`.
  This gives you a named `PortStack` plus typed “subtyping by forgetting” via capabilities (`HasPort`),
  so you can project/forget ports structurally.
- Prefer the capability surface `PortStack.HasPort` and use
  `PortStack.getObj` / `PortStack.getHom` / `PortStack.forgetPort`
  instead of manually nesting `fst`/`snd` or re-deriving `forgetProductLeft` / `forgetProductRight` chains.
- For explicit S-tier robustness checks on *any* stack over `LOG`, use:
  `LogOS/LT/Ports/PortStack/ClassicalLimit.agda` (`withClassicalLimit`, `withStrictDecode`, `strictifyStack`).
  This turns internal antisymmetry-based strictification into a uniform, typed operation.

## Bubble checks (do this frequently)

A **code bubble** is an “island” that:

- is not reachable from a curated surface (for non-Host core modules, this is a CI failure; for apps it is a discoverability smell),
- duplicates a concept that already exists elsewhere (two “almost the same” interfaces),
- cannot explain its refinement relation via a named observation (`View`),
- or forces you to violate layering (e.g. ports importing adapters, apps reaching into kernel internals).

Check for bubbles early and often:

- run `scripts/check/reachability_check.sh` when adding new core modules or moving imports,
- run `scripts/check/layer_order_check.sh` when a new dependency feels “convenient”,
- run `scripts/check/spec_ref_check.sh` when adding new `LogOS/LT/**` modules,
- run `scripts/check/api_purity_check.sh` when expanding `LogOS/API/**`.

When you find a bubble, the default move is **refactor**:

- split the island into “port interface” vs “adapter implementation” vs “app composition”,
- move code to the correct layer,
- or delete it if it does not have a justified observation boundary.

## What to avoid (hard failures of the design)

- Introducing equality-based “semantic” laws where refinement is intended.
- Defining relations not induced by a `View` unless you can justify the view discipline break.
- Hiding assumptions in globals; all doctrines belong in explicit records/parameters.
- Over-coupling ports: if two ports can be independent, keep them independent and compose by product.
- Adding new core modules without wiring reachability (API/spec) or spec sync (`LogOS/LT/**`).

## Further reading (repo-aligned)

- Ports as displayed layers: `docs/Patterns/Ports_As_Displayed.lagda.md`.
- Nested transformer stacks: `docs/Patterns/Nested_Transformer_Stacks.lagda.md`.
- Successor-stage and law-port rules: `docs/Patterns/Ports_As_Displayed.lagda.md`.
- Layering and import direction: `docs/Core/Architecture/Diagram.lagda.md` and `docs/Generated/Architecture_Layer_Order.md`.
- Port checklist: `docs/Patterns/HowTo/HowTo_Add_Port.lagda.md`.
- Spec-linked notes (literate): `docs/Core/Spec/LogicalTransformers.lagda.md`.
