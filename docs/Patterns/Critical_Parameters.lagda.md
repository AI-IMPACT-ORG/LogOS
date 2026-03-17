<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: critical parameters (phase transitions as cutpoints)

This note records a small *design vocabulary* for a recurrent shape that shows up in several
intended readings of LogOS:

- RG / coarse-graining: “beyond some scale, a property becomes stable”.
- Information theory: “beyond some noise level, a distinguishability witness disappears”.
- Complexity/opacity arguments: “below some resource/observability level, a task is impossible”.
- de Bruijn–Newman: “beyond some heat-flow time, all zeros become real”.

This repository does **not** claim proofs of GRH, P≠NP, etc. The goal is to make the *obligation
graph* explicit: what data must be supplied, and which parts are wiring that then composes.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Critical_Parameters where

import LogOS.API.LT
```

## The minimal repository-local shape

The core ingredients are:

1. A **parameter boundary** `T : ConPreorder` (time / scale / budget / noise / …).

2. A **monotone predicate** `Good : Con T → Set` meaning “the property holds at parameter `t`”.
   Monotonicity is *upward closure*: if `t ⊑ u` then `Good t → Good u`.

   (Equivalently: `Good` is a monotone map into the truth boundary; see code anchor
   `LogOS/LT/ConPreorder/Truth.agda`.)

3. A **least cutpoint** `Λ : Con T` such that `Good` holds for all parameters above `Λ`.
   This is packaged as `CriticalCut` in:

   - code anchor: `LogOS/Ports/CriticalParameter.agda` (`CriticalCut`, `SharpCut`).

The design choice is to treat “critical parameters” as **ports/assumptions** (records),
not as ambient meta-level real analysis.

## How de Bruijn–Newman fits (shape only)

Fix:

- `T = ℝ` (or another time-like parameter object),
- `Good t` = “the deformed object at time `t` satisfies the target property”
  (for zeta: “`Ξₜ` has only real zeros”).

Then the de Bruijn–Newman constant is exactly a `CriticalCut T Good`:

- `GoodAbove`: for all `t ≥ Λ`, the property holds;
- `least`: any other cutpoint must be ≥ `Λ`.

RH becomes the boundary inequality “`Λ ≤ 0`” (after choosing the time origin),
and known lower bounds become the reverse inequality. (Those inequalities are **math content**;
LogOS only supplies the shape.)

## Relation to `Flow` (normalisation doctrine)

`Flow` (`GuardedClosure`) is the repository’s primitive normalisation interface:

- code anchor: `LogOS/LT/Flow.agda` (`GuardedClosure`)
- stable-point reflection: `LogOS/LT/Reflection.agda` (`quot ⊣ evalm`)

Critical-parameter stories align with (and often generate) `Flow` stories:

- a one-parameter semigroup (heat/noise/RG) often induces an “eventual closure” / effective semantics
  that is a `GuardedClosure` (time-to-∞ or μ-generation),
- while the least cutpoint `Λ` measures “how much parameter is needed” for a particular property to hold.

LogOS keeps these layers separate on purpose:

- `Flow` is the compositional closure doctrine used everywhere,
- `CriticalCut`/`SharpCut` is the optional *quantitative* statement that a phase transition is governed by a cutpoint.

In the current repo, visibility/opacity threshold stories are packaged
downstream in `LogOS/Ports/Opacity/Profile.agda`, not in the default LT core.
Those packagings now include exact-threshold theorems that feed directly into
`CriticalCut` and `SharpCut`, and the universality pack reuses the same
cutpoint vocabulary for measured-budget agreement.
The irreversibility pack is then a downstream quantitative slice of the same
cut vocabulary, not an independent threshold doctrine.
It should reuse the existing cutpoint language rather than invent a second
resource-threshold story downstream.

## Interpretation discipline

Critical-parameter language is structurally generic. To avoid overclaiming:

1. keep the structural theorem or pack definition domain-neutral,
2. introduce an explicit bridge record for any named external reading,
3. state only conditional “X-shaped” or “X-route obstruction” corollaries until
   the full domain semantics is mechanised.

Current canonical code anchors for this vocabulary:

- `LogOS/Ports/CriticalParameter.agda`
- `LogOS/Ports/Opacity/Profile.agda`
- `LogOS/Apps/Universality/Agreement/Universal.agda`
- `LogOS/Apps/Universality/Architecture.agda`
