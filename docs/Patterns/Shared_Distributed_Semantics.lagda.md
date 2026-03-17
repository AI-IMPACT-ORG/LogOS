<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: shared distributed semantics discipline

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Shared_Distributed_Semantics where

import LogOS.API.LT
```

This repo uses “logical transformers” as a general packaging for compositional models.
When we want to talk about *physics-like* modelling (and PL/concurrency models inspired by physics),
we want **locality** and **causality** to be the path of least resistance *without* turning them into
global axioms of the kernel.

This document records the design choice for a *shared distributed semantics* discipline in v1.1:

- **shared**: one fixed interface semantics (one boundary type, one causal doctrine);
- **distributed**: combined observation is a *tuple* of local readouts, indexed by regions/observers.

The core kernel remains more general; this is a *curated discipline* for packs.

## Concrete v1.1 definition (what the shared semantics discipline means here)

Pick once (this is an explicit modelling choice):

1. a locality index type `I` (regions / observers / subsystems),
2. a *local observation family* `O : I → ConPreorder` (local constraints/specs may depend on the region),
3. a *local doctrine family* `GC₀ : (i : I) → GuardedClosure (O i)` (the “laws” at each region).

Then the *shared, distributed* boundary is definitionally:

- `B = LocalBoundary I O = DFunPreorder I O`
  (carrier `Con B = (i : I) → Con (O i)`; often written `Π i → O i` in prose).

And the *shared, distributed* causal doctrine is:

- `GC = pointwiseClosure GC₀ : GuardedClosure B` (closure/law applied per index).

Uniform special case (inline constant-family specialisation):

- take `O = λ _ → O₀` and `GC₀ = λ _ → GC₀₀`, recovering `LocalBoundary I O₀ = FunPreorder I O₀`
  and `pointwiseClosure (λ _ → GC₀₀)`.

Now a **transformer in this shared distributed semantics discipline** is:

- any kernel whose boundary is `B`, equipped with the closure `GC`,
  i.e. an object of the flow-equipped category `LogOS.LT.LOG.Flow2Cat.WithPort` with that fixed closure.

In practice, you typically present such a kernel by giving a `LocalityPort` and using `localKernel` to build the kernel
boundary/readout.

Code anchors:

- Shared distributed semantics record: `LogOS/Ports/PhysicalSemantics/Core.agda`
- Dependent locality boundary + port packaging (canonical): `LogOS/Ports/Locality/Core.agda`
- Generic realisation-family pattern: `LogOS/Ports/Realisations/DependentStack.agda`
- Representation theorem (probe suites ↔ distributed views): `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`
- Causal doctrine (Flow/closure): `LogOS/LT/Flow.agda`
- Flow preservation on translations: `LogOS/LT/HomFlow.agda` / `LogOS/LT/LOG/Flow2Cat.agda`
- Stable completion (closure-gated self-reference): `LogOS/LT/Theorems/StableCompletion.agda`

## The important distinction: shared vs per-system causality

The library supports two patterns:

1. **Per-system closure (generic):** each kernel carries its own `GuardedClosure` on its boundary.
   This is what `LogOS.LT.LOG.Flow2Cat.WithPort` implements in full generality.

2. **Shared closure (shared distributed semantics discipline):** you fix `I`, `O`, and `GC₀` once, lift it
   pointwise, and then only consider systems living over that shared boundary + doctrine.

Both are useful. The second one is what lets you treat these systems as living in the same
semantics, and the repository term “physical transformer” refers to this case.

**Global coherence is not automatic**: if you want a single coherent semantics, you must fix the
shared boundary/doctrine and keep translations honest (typically, they should not silently relabel
the interface).

## Dependency injection of meaning (self-similarity, not self-reference)

In v1.1, the shared distributed-semantics ledger is not a kernel axiom; it is a record you pass around explicitly.
This is a deliberate dependency-injection point for meaning:

- you choose `(I, O, GC₀)` once (what counts as a region, an observable, and a local law),
- downstream constructions are parameterised by that choice.

In particular:

- `LogOS/Ports/Realisations/DependentStack.agda` is the generic shared-boundary / many-realisations pattern once
  `PS : DependentLocalSemantics` is fixed.
- `LogOS/Ports/AbstractDeutsch2Cat.agda` is one downstream displayed/law-port construction over that same ledger,
  used when the mathematical story specifically needs the Deutsch locality + local reversibility stack.
- The uniform case is recovered by choosing constant families of observables and doctrine
  (`O = λ _ → O₀`, `GC₀ = λ _ → GC₀₀`).

The Deutsch-specific construction then builds:

- a shared distributed-semantics thin 2-category (code: `LogOS.Ports.AbstractDeutsch2Cat.Deutsch2CatLocal.Locality.WithPort`),
- law-ports over it (causality + local reversibility),
- their port product (the Deutsch-style category) via the same displayed/totalisation recipe.

So the codebase is self-similar in shape, but domain meaning enters only through such explicit injection
points (not by self-reference).

In distributed (function-shaped) boundaries, it is common to prove correspondences pointwise and only later
assemble them into strict global equalities. In v1.1 this strictification step is packaged explicitly as:

- `LogOS/Ports/Globalise.agda` (`Globalise I X`)
- add this only when a downstream pack genuinely needs strict global equality
  rather than pointwise refinement or equivalence

## Irreversibility and thermodynamic layering

The post-refactor physical story keeps the same discipline:

- the Deutsch-style category still means locality + causality + local reversibility,
- there is also a broader causal physical slice with no pointwise-locality
  restriction on arrows,
- thermodynamic cost is an extra law-port over that causal slice,
- irreversibility is detected by collapse of distinguishable local observations, not by baking a new primitive into the kernel.

Code anchors:

- general causal slice: `LogOS/Ports/AbstractCausal2Cat.agda`
- minimal irreversibility-facing thermodynamic layer:
  `LogOS/Ports/AbstractCausalLandauer2Cat.agda`
- generic obstruction theorems: `LogOS/LT/ConPreorder/Isomorphism.agda`
  and `LogOS/Ports/AbstractDeutsch2Cat/Reversibility.agda`
- flagship example: `LogOS/Apps/Irreversibility/BitResetDeutsch.agda`
- optional opacity/factorisation pack: `LogOS/Ports/Opacity.agda`
- physical lower-bound bridge: `LogOS/Ports/AbstractLandauerObservational.agda`
- bridge-backed lower-bound example: `LogOS/Apps/Irreversibility/BitResetLandauer.agda`

Important distinction:

- a total reset map can live on the causal physical base and carry an explicit Landauer-style cost layer,
- but it does **not** automatically live in the Deutsch stack, because that stack already requires a local reversibility witness.

So the intended reading is:
Deutsch gives the reversible capability layer; causal + Landauer gives the
default thermodynamic stack for irreversible arrows; and the narrower
Deutsch + Landauer slice is only for arrows that already lie in `LOGᴰ`.

In the current repo, the first quantitative irreversible-information layer is
still boundary-first and now lives in the optional opacity pack:

- choose an explicit finite observed family,
- witness finite loss under a factorised public observation,
- exclude local reversibility,
- and only then apply an explicit bridge assumption to obtain a lower bound on
  actual Landauer cost, with chosen `CostBound`s as a derived corollary.

## Why this is the smallest useful choice

It is minimal (no new kernel axioms), but sufficient to express:

- Locality is a boundary type choice (`DFunPreorder I O`, carrier `(i : I) → Con (O i)`), not an extra axiom.
- Causality is a single closure doctrine (`Flow`) plus one preservation inequality on translations.
- The interface is “physics-like” by construction: combined observation is built from local probes.

This is strong enough to host a Church–Turing–Deutsch style principle *as an explicit assumption pack*:
pick a universal simulator kernel over the same shared boundary (often `programKernel` of a chosen
stack of primitives), and require every physical system to admit a semantics-preserving simulation
into it, with any approximation/resource story made explicit as additional ports/contracts.

Code anchor (assumption-scoped ledger + concrete instance):

- `LogOS/Ports/Universality/CTD/Ledger.agda`
- `LogOS/Apps/Universality/CTD.agda`
- Categorical packaging over the shared distributed-semantics ledger (Deutsch-style category via local reversibility):
  `LogOS/Ports/AbstractDeutsch2Cat.agda`

## Tooling loop theorem: causality checking reduces to local obligations

If you keep translations **local by construction** (boundary map is pointwise), then flow preservation
against the shared, distributed doctrine is discharged pointwise:

- prove `mapAt i (Flow (GC₀ i) c) ≼ Flow (GC₀ i) (mapAt i c)` for each region `i`, and you get
  `map∂ (Flow c) ≼ Flow (map∂ c)` for the induced boundary action `map∂`.

Code anchor: `LogOS/Ports/PhysicalTransformers.agda`
(`pointwiseMap-preservesFlow`, `mkKernelHomFlow`).

This pointwise tooling is a convenience surface, not the full physical base:
for genuinely neighbourhood-dependent or otherwise non-pointwise arrows, use
the broader causal slice `LogOS/Ports/AbstractCausal2Cat.agda`.

Boundary enrichment / functoriality across *different* local languages (same index `I`, different `O₁ → O₂`)
uses the parallel pair:

- `pointwiseMap-preservesFlow`
- `mkKernelHomFlow₂`

Practical workflow:

1. Fix `(I, O, GC₀)` once per semantics, where `O : I → ConPreorder … …` and `GC₀ : (i : I) → GuardedClosure (O i)`.
2. Present each system as a `LocalityPort` (and/or the derived kernel `localKernel`).
3. For an adapter, implement a pointwise boundary map `mapAt : (i : I) → Con (O i) → Con (O i)`.
4. Prove causality locally: `mapAt i (Flow (GC₀ i) c) ≼ Flow (GC₀ i) (mapAt i c)` for each `i`.
5. Assemble the boundary-wide certified adapter with `mkKernelHomFlow`.

If your adapter *changes* the local observable language (boundary enrichment), replace `O` by `(O₁, O₂)`,
provide `mapAt : (i : I) → Con (O₁ i) → Con (O₂ i)`, and use `mkKernelHomFlow₂`.

The repo now factors this discipline through a generic surface:
`LogOS/Ports/Realisations/DependentStack.agda` factors out the
“one shared boundary, many realisations” pattern. Downstream packs then choose
their own locality index `I`, local preorders `O`, and closure family `GC₀`
without changing the kernel core.

Code anchors:

- generic surface: `LogOS/Ports/Realisations/DependentStack.agda`
- architecture corner + canonical denotations: `LogOS/Ports/Realisations/Architecture.agda`

Concurrency anchor (minimal happens-before closure example):

- `LogOS/Apps/Concurrency/HappensBefore.agda`

This file is now the canonical shared-boundary specialization downstream of the
generic `DependentStack` pattern: the app-specific content is the chosen
happens-before preorder, closure, and race-freedom predicate, not a second
architecture.
If you want another shared-boundary app, start by copying this specialization
pattern rather than adding a new app-local architecture layer.

## Representability-flavoured denotation (why “boundary-first” is not mere bookkeeping)

Once you fix the shared boundary `B = LocalBoundary I O` (uniform special case: choose `O = λ _ → O₀`, so
`B = FunPreorder I O₀`), there is a canonical “denotation” kernel with:

- `Code = Con B` (the boundary itself),
- `decode = id`.

Every kernel over `B` then has a canonical adapter into this
denotation (`decode` itself). The key fact is now a genuine classification:

- transparent denotations into the boundary-as-code kernel over one fixed
  transparent boundary map now form a centered fibre,
- the canonical denotation is the center of that fibre, and
- any two such denotations contract to the same canonical normalized code, so
  no semantic fork remains after normalization.

The older comparison theorems remain as the boundary-facing ingredients that
identify the normalized code semantics with the kernel's own local code
preorder and equivalence.

This is representability-flavoured (universal-property in shape), but stated at the level of
LogOS kernels/adapters.

Code anchors:

- dependent boundary: `LogOS/Ports/BoundaryAsCode.agda`
  (`canonicalTransparentDenotationPackage`, `transparentDenotationFiber`,
  `transparentDenotationNoFork`, `transparentDenotation↔localCodePreorder`,
  `transparentDenotation≈localCodePreorder`).

Strict function equalities are gated behind explicit global coherence (`DependentGlobalise` / `Globalise`).

## Note: granularity (keep it explicit)

For granularity distinctions (and why coarse-graining is usefully treated as an explicit
translation/port between boundaries), see the guide:

- `docs/Patterns/HowTo/HowTo_Build_Logic_Transformer_Architecture.lagda.md` (“Physical transformers”).
