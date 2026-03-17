<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: opacity factorisation

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Opacity_Factorisation where

import LogOS.API.LT
import LogOS.API.Opacity
import LogOS.API.Ports.Physical
import LogOS.Apps.Irreversibility.All
import LogOS.Apps.Opacity.All
```

This note records the explicit **opacity pack** formulation of the
observational-compression story.

## Design choice

The generic center is now:

- factorisation of observations,
- distinguishability of explicit finite families under a chosen observation,
- loss of distinguishability under a coarser factorised observation,
- obstruction to faithful public readback,
- finite count loss only as a derived example-layer consequence.

This is intentionally **not** part of the default LT spine.

The only new LT-level seam is:

- `LogOS/LT/View/Factorisation.agda`

Everything else lives in the optional opacity pack:

- `LogOS/Ports/Opacity/Port.agda`
- `LogOS/Ports/Opacity/Factorisation.agda`
- `LogOS/Ports/Opacity/Distinguishability.agda`
- `LogOS/Ports/Opacity/Obstruction.agda`
- `LogOS/Ports/Opacity/Profile.agda`
- `LogOS/Ports/Opacity/FiniteCompression.agda`
- explicit opt-in API: `LogOS/API/Opacity.agda`

## What is defined

The pack surface is split on purpose.

- `Port`
  - `OpacityPort`
  - `toView`, `fromView`
  - `opacityKernel`
  - `OpacityPreorder`
- `Factorisation`
  - `OpacityFactorisation`
  - its wrapped LT seam `FactorisesThrough`
- `Distinguishability`
  - `ObservedFamily`
  - `DistinguishableFamily`
- `Obstruction`
  - `OpaqueFamily`
  - `PublicReadbackOn`
  - `FaithfulPublicObservationOn`
  - `opaqueFamily-obstructsPublicReadbackOn`
  - `opaqueFamily-obstructsFaithfulPublicObservationOn`
- `Profile`
  - `ObservationProfile`
  - `DistinguishableAt`
  - `OpaqueAt`
  - `CriticalOpacity`
  - `CriticalVisibility`
- `FiniteCompression`
  - `FiniteCompressionWitness`
  - `finiteLoss-count≤`
  - `finiteLoss-strictGap`

## Mathematical reading

The pack is phrased entirely in the preorder/view language already present in
the spine.

- Private and public semantics are just two views on the same carrier.
- Opacity is not hidden meta-level intent; it is an explicit factorisation from
  the private view through a coarser public view.
- Distinguishability is not equality on the carrier; it is separation under the
  chosen private observation.
- Readback obstruction is family-local and observation-relative.

This keeps the design aligned with the repo’s refinement-first stance:
information loss is witnessed at the level of observable constraints, not by
ambient extensional equalities.

## Derived finite-loss layer

`FiniteCompressionWitness` exists so the current irreversibility examples can
continue to speak in a small count-loss vocabulary.

That layer is **derived**, not primitive:

- factorisation + distinguishability + explicit public image data
  give finite compression,
- finite compression gives the count theorems
  `finiteLoss-count≤` and `finiteLoss-strictGap`.

No probability, Shannon entropy, or ambient thermodynamic semantics is built
into this pack.

## Downstream physical bridge

The physical cost story remains downstream-only:

- `LogOS/Ports/AbstractLandauerObservational.agda`

Its inputs now come from the opacity pack’s derived finite-loss layer rather
than from an LT-level compression theorem family.

So the architecture is:

- LT provides the tiny factorisation seam,
- the opacity pack provides the observation-loss vocabulary,
- the Landauer bridge adds a physical interpretation on top.

## Examples

- `LogOS/Apps/Opacity/TagOpacity.agda`
  shows hidden-tag opacity as factorised public observation.
- `LogOS/Apps/Irreversibility/BitResetCompression.agda`
  packages reset as a finite-loss witness.
- `LogOS/Apps/Irreversibility/BitResetLandauer.agda`
  shows how a chosen bridge turns that witness into a lower bound on actual
  Landauer cost, and hence on any displayed `CostBound`.
- `LogOS/Apps/Irreversibility/MeasurementCoarseGrainCompression.agda`
  shows the same structure on a measurement-style example.

## What is not claimed

- this pack is **not** part of the default LT curated surface,
- this pack is **not** a general theorem center for all downstream readings,
- this change set does **not** add probability or Shannon-style entropy,
- this change set does **not** formalise complexity theory or analytic number
  theory inside LogOS.

## Interpretation discipline

To guard against interpretation games, downstream claims must keep three layers
separate:

1. structural theorem or pack definition,
2. explicit bridge record into a named domain reading,
3. conditional corollary stated as “X-shaped” or “X-route obstruction”.

The repo should not state an “X theorem” unless the full domain semantics has
actually been mechanised.
