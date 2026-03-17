<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Path hook: physics

Goal: land on the physics-facing route named from the top-level README.

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Paths.Physics where

import LogOS.API.LT
```

This hook page gathers the existing physics-facing reading, which is otherwise
split between the systems path, the systems/physics view, and the explicit
physics ports.

Start here
----------

- Overview + conceptual spine: `docs/Core/Orientation/LogOS_Overview.lagda.md`
- Systems/physics umbrella view: `docs/Interpretations/Views/Systems_And_Physics.lagda.md`
- Systems path (architecture-first companion): `docs/Interpretations/Paths/Systems.lagda.md`

Physics-facing surfaces
-----------------------

- Reader-facing optional-physics API:
  `LogOS/API/Ports/PhysicalOptional.agda`
- Curated subroutes:
  `LogOS/API/Ports/PhysicalOptional/Causal.agda`,
  `LogOS/API/Ports/PhysicalOptional/Landauer.agda`,
  `LogOS/API/Ports/PhysicalOptional/Deutsch.agda`,
  `LogOS/API/Ports/PhysicalOptional/PreQuantum.agda`
- Pedantic export note: these curated subroutes now expose the actual
  categorical surfaces they name, including the displayed/total categories,
  forgetful functors, and uniqueness-first port accessors, rather than only
  fragments of the underlying implementation modules.
- Shared-boundary / many-realisations pattern:
  `LogOS/Ports/Realisations/DependentStack.agda`
- Locality and distributed semantics:
  `LogOS/Ports/Locality/Core.agda`, `LogOS/Ports/PhysicalSemantics/Core.agda`
- Raw implementation anchors for the optional packs:
  `LogOS/Ports/AbstractCausal2Cat.agda`,
  `LogOS/Ports/AbstractCausalLandauer2Cat.agda`,
  `LogOS/Ports/AbstractLandauerObservational.agda`
- Deutsch-style reversible slice and causal prequantum entrypoint:
  `LogOS/Ports/AbstractDeutsch2Cat.agda`,
  `LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda`

Pedantic note: the prequantum entrypoint is now named for its actual base:
`AbstractCausalPreQuantum2Cat` stacks purification over the causal + Landauer
surface, not over the narrower reversible Deutsch slice.

One concrete pack
-----------------

- Minimal measurement-style example: `LogOS/Apps/Physics/MeasurementExample.agda`

Quantitative note
-----------------

- The Landauer route is refinement-first on purpose.
- Quantitative comparison of Landauer witnesses is exported as an explicit
  preorder surface on both fibre witnesses and total decorated morphisms, not
  as equality of chosen bounds.
- The observational bridge is an explicit calibrated count-to-scale valuation
  into the ambient join-prequantale, together with a lower-bound axiom.

Boundary reminder
-----------------

- No ambient Hilbert-space, amplitude, Born-rule, or global unitarity story is
  built into the core; those are downstream readings over explicit ports.
