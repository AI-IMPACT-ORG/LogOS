<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# How to Use Existing Architecture Machinery (Practical Tips)

This note is the practical companion to
`docs/Patterns/HowTo/HowTo_Build_Logic_Transformer_Architecture.lagda.md`.

The architecture guide explains how to build a correct new layer.
This note answers a different question:

- if the lower-rung machinery already exists, how do you avoid rederiving it downstream?

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.HowTo.HowTo_Practical_Architecture_Tips where

import LogOS.API.LT
```

## 1) Add one canonical object, not one app-local story

If a new downstream example fits an existing generic family, add the smallest
canonical lower-rung object that expresses it, then let the app consume that
object.

Universality is now the model case.

Practical rule:

- when adding a new paradigm, start by defining one canonical `FuelAdapter`
  value under `LogOS/Adapters/Universality/*`;
- do not start by extending `LogOS/Apps/Universality/*` with a bespoke bridge.

Why this matters:

- the adapter value can then feed the canonical adapter deck in
  `LogOS/Apps/Universality/Stack.agda`;
- the same deck drives the CTD ledger in `LogOS/Apps/Universality/CTD.agda`;
- the same deck drives the measured-agreement family in
  `LogOS/Apps/Universality/Agreement/Universal.agda`;
- the same deck is exposed through the flagship app surface in
  `LogOS/Apps/Universality/Architecture.agda`;
- the same adapter family lives in both `Flow + Budget` stack readings:
  `LogOS/Ports/Universality/FlowBudget2Cat.agda` and
  `LogOS/Ports/Universality/ArchitectureFlowBudget2Cat.agda`.

Concrete anchors:

- `LogOS/Ports/Universality/Core.agda`
- `LogOS/Apps/Universality/Stack.agda`
- `LogOS/Apps/Universality/Architecture.agda`
- `LogOS/Adapters/Universality/Minsky.agda`
- `LogOS/Adapters/Universality/Lambda.agda`
- `LogOS/Adapters/Universality/EVM.agda`

Practical anti-pattern:

- “I only need one theorem for one paradigm, so I will add a local
  `kernel -> universal` bridge in the app.”

In this repository that is usually the wrong move. If the bridge is generic,
put it in the lower rung and let the app read off the consequence.

Fast executable template:

- `LogOS/Checks/UniversalityAdapterTemplate.agda`

## 2) If several systems share one boundary, start from the shared-boundary pattern

If your examples differ mainly in implementation, scheduler, local law, or
realisability data, but they share one boundary, use the shared-boundary /
many-realisations pattern first.

Canonical anchors:

- `LogOS/Ports/Realisations/DependentStack.agda`
- `LogOS/Ports/Realisations/Architecture.agda`
- `LogOS/Ports/Locality/Core.agda`
- `LogOS/Ports/BoundaryAsCode.agda`

Concurrency is the reference downstream specialization:

- `LogOS/Apps/Concurrency/HappensBefore.agda`

Practical rule:

- if the real domain choice is “which closure / predicate / local preorder do I
  put over one shared boundary?”, then the app should look like a specialization
  of `DependentStack`, not like a second architecture.

This is stronger than a stylistic preference.
It means transport, no-fork, and shared-boundary comparison stay inherited from
the generic machinery instead of drifting app-locally.

Good signs that you are on the right track:

- the app-specific part is visibly just:
  - one boundary preorder,
  - one closure or doctrine,
  - one predicate of interest;
- the transport theorem reads as a specialization of the generic shared-boundary
  transport story;
- two implementations can be compared because they live over the same explicit
  boundary, not because the app silently bakes in a comparison relation.

## 3) Small apps should be layered slices, not mini-frameworks

Not every app needs a full stack deck.
If a downstream example only uses one observation layer plus one extra doctrine,
write it as that layered slice and stop.

Current examples:

- physics: `LogOS/Apps/Physics/MeasurementExample.agda`
- opacity: `LogOS/Apps/Opacity/Demo.agda`
- opacity with factorisation: `LogOS/Apps/Opacity/TagOpacity.agda`
- irreversibility: `LogOS/Apps/Irreversibility/BitResetLandauer.agda`

Practical rule:

- if the app really is “one observation layer + one telemetry / contract /
  quantitative layer + one witness”, say that directly;
- do not invent an app-local architecture vocabulary to make the example look
  bigger.

In practice this usually means:

- use `OpacityPort` directly for single-view observation layers;
- use `AgreementPort` directly for two-view comparison layers;
- use `IOPort` only when there is a real telemetry / admissibility / interaction
  layer;
- read quantitative consequences through the existing threshold and cut
  vocabulary rather than inventing an app-local resource story.

The point is not minimal code for its own sake.
The point is to let readers see that the app is a thin slice of the same global
discipline.

Fast executable template:

- `LogOS/Checks/SmallLayeredSlice.agda`

## 4) Prefer a deck when one object drives several downstream readings

Use a curated app-side deck when one lower-rung object simultaneously determines
several downstream interpretations.

This is exactly why `LogOS/Apps/Universality/Architecture.agda` exists.

Use a deck when:

- one adapter family drives several app-level stories;
- one stack basis is read in more than one mathematically meaningful way;
- one pack wants to present one coherent public route through several lower-rung
  modules.

Do not add a deck when:

- the app only demonstrates one layered slice;
- the “deck” would merely be a collector record with one field;
- the file would rephrase existing canonical modules without clarifying the
  architecture.

Rule of thumb:

- add a deck when it compresses several consequences into one honest surface;
- avoid a deck when it only renames imports.

## 5) Let apps advertise the right role

The pack entrypoint should say what role the app plays relative to the
architecture.

Good examples after the current refactors:

- universality:
  `LogOS/Apps/Universality/All.agda`
  says the pack is the flagship stacked-transformer architecture showcase;
- concurrency:
  `LogOS/Apps/Concurrency/All.agda`
  says the pack is the shared-boundary / many-realisations specialization;
- ZFC:
  `LogOS/Apps/ZFC/All.agda`
  reads as the heavy stack-first application rather than the architecture
  tutorial.

Practical rule:

- one flagship pack should teach the architecture;
- one or two medium packs should show real specialization;
- small packs should show thin slices;
- heavy packs should show stress-tested downstream consequence, not tutorial
  pedagogy.

## 6) A short downstream checklist

When writing or refactoring an app:

1. Ask whether the real new content is:
   - a new port,
   - a new adapter,
   - a new stack/deck,
   - or only a new downstream witness.
2. If the app shares a boundary with other examples, start from
   `DependentStack`.
3. If the app shares a one-view or two-view observation story, use
   `OpacityPort` or `AgreementPort` directly.
4. If one canonical object drives several app-level readings, add or extend a
   deck.
5. If the file mostly aliases existing theorems, push those aliases down or
   delete them.
6. Let the app text say whether it is:
   - a flagship architecture deck,
   - a shared-boundary specialization,
   - a small layered slice,
   - or a heavy downstream stress test.

## 7) Copy-this-pattern checklist

If you want the shortest practical path, start from one executable template:

- universality-style adapter path:
  `LogOS/Checks/UniversalityAdapterTemplate.agda`
- small layered-slice path:
  `LogOS/Checks/SmallLayeredSlice.agda`

Then:

1. keep the lower-rung object canonical;
2. consume it from the app instead of rebuilding the bridge;
3. use warm lanes while iterating;
4. finish on `make check-all`.

If you want a copyable starting point instead of prose, begin from:

- `LogOS/Checks/UniversalityAdapterTemplate.agda` for the adapter/deck route
- `LogOS/Checks/SmallLayeredSlice.agda` for the small layered-slice route

## What this note is not claiming

- It does not claim every app should be a `stack2Cat`.
- It does not claim every downstream example should be collapsed into
  universality.
- It does not claim lower-rung machinery always decides every app design
  question.

The practical claim is narrower:

- when the machinery already exists, use it directly and let the app specialize
  it honestly.

## Copy-This Pattern

If you want the shortest safe downstream recipe, copy this sequence:

1. add one canonical lower-rung object;
2. check whether it already fits an existing deck or shared-boundary pattern;
3. let the app specialize that machinery directly;
4. add only the domain-specific witness or predicate that the app contributes;
5. stop before inventing a second architecture vocabulary.
