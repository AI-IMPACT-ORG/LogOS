<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# View family: Systems and Physics

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Views.Systems_And_Physics where

import LogOS.API.LT
```

This umbrella view collapses the earlier systems-engineering,
control-and-cybernetics, and physics notes into one reader-facing surface.

What is actually defined
------------------------

- **Systems engineering**: kernels as components with explicit interfaces, and
  ports as capability/law layers with canonical forgetting.
- **Control / cybernetics**: observation boundaries, closure/flow doctrines,
  and contracts for additional obligations.
- **Physics-facing layers**: locality, causality, reversibility, cost, and
  opacity as optional ports over the same transformer spine.
- **Telemetry-facing layers**: input-indexed observations via `IOPort`, with
  adequacy formulated as reflection of output refinement from admissible tests.
- **Quantitative irreversibility-facing layers**: under an explicit
  observational cost bridge and a chosen calibrated count valuation into the
  ambient join-prequantale, finite observational loss can be turned into lower
  bounds on actual Landauer cost; chosen displayed `CostBound`s are then
  derived corollaries, and unit-loss remains derived by refinement rather than
  primitive by propositional equality.

Literature reading
------------------

- a kernel is a component with an observed interface and a transportable
  semantics;
- ports are typed capability/compliance layers, and stacks are composed
  architectures with explicit projections;
- `Flow` can be read as stabilisation/update discipline, and additional
  physical meaning comes from explicit locality/causality/reversibility/cost
  layers rather than from ambient structure.

Where LogOS is weaker or more general
-------------------------------------

- interfaces are logical/refinement objects, not tied to one hardware or
  software notion;
- there is no built-in time model, controller synthesis algorithm, or state
  space semantics;
- “reversibility” and “cost” are explicit optional law ports, not global
  semantics of every kernel.

What is not claimed
-------------------

- no full MBSE/SysML replacement or automatic architecture synthesis;
- no theorem of controllability, observability, or robust control by default;
- no Hilbert-space, amplitude, or Born-rule semantics in the core.

Code anchors
------------

- `LogOS/API/Ports/PhysicalOptional.agda`
- `LogOS/API/Ports/PhysicalOptional/Causal.agda`
- `LogOS/API/Ports/PhysicalOptional/Landauer.agda`
- `LogOS/API/Ports/PhysicalOptional/Deutsch.agda`
- `LogOS/API/Ports/PhysicalOptional/PreQuantum.agda`
- `LogOS/LT/Kernel.agda`
- `LogOS/LT/Contracts.agda`
- `LogOS/LT/Ports/PortSig.agda`
- `LogOS/LT/Ports/PortStack.agda`
- `LogOS/LT/Flow.agda`
- `LogOS/Ports/IO.agda`
- `LogOS/Ports/PhysicalSemantics/Core.agda`
- `LogOS/Ports/PhysicalTransformers.agda`
- `LogOS/Ports/AbstractCausal2Cat.agda`
- `LogOS/Ports/AbstractCausalLandauer2Cat.agda`
- `LogOS/Ports/AbstractLandauerObservational.agda`
- `LogOS/Ports/Opacity/FiniteCompression.agda`
- `LogOS/Ports/PreQuantum/AbstractCausalPreQuantum2Cat.agda`
- `LogOS/Apps/Physics/MeasurementExample.agda`
- `LogOS/Apps/Opacity/TagOpacity.agda`
- `LogOS/Apps/Irreversibility/BitResetLandauer.agda`

These smaller packs are intentionally not second architecture worlds. They are
downstream slices over the same transformer discipline:

- the curated entrypoint is `LogOS.API.Ports.PhysicalOptional`, while the raw
  `LogOS.Ports.Abstract*` modules remain implementation anchors,
- the curated causal, Landauer, and prequantum subroutes now expose the actual
  displayed/total categorical surfaces and forgetful structure they refer to,
- `MeasurementExample` is the minimal `OpacityPort + IOPort` layering,
- the opacity examples are single-view boundary slices,
- the Landauer example is the quantitative downstream of
  opacity/compression plus an explicit bridge to actual cost.

For the bit-reset example specifically, the bridge is now fixed-process rather
than falsely global: the observation data is stated exactly for the chosen
reset map, which is the honest abstraction boundary currently supported by the
example.
