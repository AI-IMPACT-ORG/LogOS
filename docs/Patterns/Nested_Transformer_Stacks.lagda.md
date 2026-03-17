<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: nested transformer stacks

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Nested_Transformer_Stacks where

import LogOS.API.LT
```

The core mathematical pattern is recursive:

- a **kernel** is a transformer on its boundary preorder;
- a module is often a **decorated transformer** (flow, contract, encode, etc.);
- decorators are expressed as `DisplayedThin2Cat` over an explicit base thin 2-category;
- totalisation produces a new transformer class with the same kernel-level observations.

This keeps the system engineered for **weakly coupled layers**:

- each layer carries its own boundary obligations;
- coupling across layers is always via explicit projection functors;
- refinement remains inherited from base `LOG` (2-cells are boundary-driven observational refinements, `_⇒∂_`) unless explicitly re-defined.

## Why this is the library’s standard stack shape

The stack pattern is implemented directly in two steps:

1. define a displayed layer `D : DisplayedThin2Cat C … …` for the extra structure on a chosen base `C`;
2. take `DecoratedThin2Cat D` to obtain a new thin 2-category of modules with that structure.

The one-step packaged form of this move is now explicit as
`LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`: a successor stage is just a
displayed layer together with its Σ-totalisation and inherited-refinement
projections.

Composition of independent ports is then a purely structural choice (`PortStack`), not a new proof principle.
`PortStack` folds (definitionally) to a right-associated `ProductDisplayed`, but also gives a typed
capability/projection discipline (“structural subtyping by forgetting”) by construction.

Code anchors:

- tags + port signatures: `LogOS/LT/Ports/PortSig.agda`
- stacks + projections/forgetting: `LogOS/LT/Ports/PortStack.agda`
- one-step successor-stage packaging: `LogOS/LT/DisplayedThin2Cat/SuccessorStage.agda`

## Static stacks vs generated hierarchies

The same step appears in two different roles inside LogOS:

- **static stacked decorations**: choose a finite displayed layer once, then totalise once (`PortStack`, `Singleton2Cat`, `Stack2Cat`);
- **generated successor stages**: reuse that same one-step totalisation repeatedly to build a cumulative hierarchy (`SuccessorStage`);
- **generated closures/effectivity**: use explicit Kleene-generation data to build a guarded closure/effectivity doctrine (`LogOS/LT/Sup/AbstractGeneratedClosure.agda`, `LogOS/LT/Effectivity.agda`);
- **stable completion**: only after a closure has been chosen, cap the semantic story by factoring into stable points (`LogOS/LT/Theorems/StableCompletion.agda`).

Pedantic boundary: this is **not** a generic fixed-point theorem about thin
2-categories. The generated ladder lives in explicit boundary/preorder data,
and stable completion is a closure-gated semantic cap, not a replacement for
stage generation.


## Practical naming rule for projections

The current v1.1 convention is capability-first (to reduce the “projection zoo”):

- each port module exports a single record value (`port2Cat`/`stack2Cat`) and `open … public` to expose
  the uniform surface: `Displayed`, `WithPort`, `forget`, `stack`, and `port` (capability).
- projections are structural and uniform:
  - underlying object: `PortStack.baseObj` with the exported `stack`,
  - underlying hom: `PortStack.baseHom` with the exported `stack`,
  - payload: `PortStack.getObj` / `PortStack.getHom` with the exported `port` capability.
- avoid bespoke `…KernelOf`/`…PortOf` wrappers unless they add non-trivial behaviour (not mere Σ-projections).
  If a domain needs named projections, define them in the domain pack (Apps) rather than in the port spine.

Example anchors:

- singleton port (`Flow`): `LogOS/LT/LOG/Flow2Cat.agda` exports `WithPort`, `forget`, `stack`, `port`.
- composite stack (`Flow + Contract` over `LOGᴳ`): `LogOS/LT/LOG/ArchitectureFlowContract2Cat.agda` exports `stack`, `WithPort`, `forget`,
  and capability requirements `flow` / `contract` (as `HasPort …`).

## Consequence for the Flow + Contract architecture stack

The flow + contract stack in `LogOS/LT/LOG/ArchitectureFlowContract2Cat.agda` is no longer a side construction:

- flow and contract are encoded as the same displayed-composition mechanism used by all doctrine layers;
- stack-level accessors make the module boundary explicit in downstream code;
- the layer remains weak because 2-cells are still boundary refinements (inherited from base `LOGᴳ`).

In 1.1, this stack is implemented via `PortStack`, so:

- the displayed layer is definitionally a `ProductDisplayed` (discipline proofs remain `refl`),
- port projections are capability-driven and uniform (`HasPort` / `forgetPort`),
- additional robustness checks can be stacked uniformly (e.g. strictification via
  `LogOS/LT/Ports/PortStack/ClassicalLimit.agda`).

## Pack-level semantics/family pattern (weak coupling in practice)

For application packs, the same weak-coupling idea should be visible at the module boundary:

- a semantics ledger names the designer-chosen boundary/preorder/doctrine;
- a realisation family presents the shared-boundary operations;
- the architecture surface derives the canonical apex and denotations.

Generic shared-boundary surface: `LogOS/Ports/Realisations/DependentStack.agda`.
Pack-level architecture pattern (dependent-first): `LogOS/Ports/Realisations/Architecture.agda`.

Related “refinement” pattern (boundary enrichment without kernel changes):

- choose a closure (nucleus-style) (`Flow`) to define effective observables (`Flow ∘ decode`);
- optionally add guarded self-reference (`QuotePort`) to reify effective boundary constraints as code.

Code anchors: `LogOS/LT/Theorems/EffectivePackets.agda`, `LogOS/LT/LOG/QuotePort2Cat.agda`.

Curated ZFC-facing entrypoint using the same ledger/deck discipline:
`LogOS/Apps/ZFC/Stack/ReifiedTower.agda`.
