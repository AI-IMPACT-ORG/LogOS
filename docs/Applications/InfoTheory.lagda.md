<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Information Theory (Shannon + DPI/Capacity/ThermoRG)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.InfoTheory where

-- Sync guard: these imports anchor the pack surfaces referenced in this note.
-- If they drift, the docs build fails.
import LogOS.Packs.InfoTheory.Surface
import LogOS.Packs.InfoTheory.Applications.All

-- Identifier sync guards (claim-heavy): these names are referenced in the prose.
import LogOS.Packs.InfoTheory.Applications.DPI      as DPIApp
import LogOS.Packs.InfoTheory.Applications.Capacity as CapApp
import LogOS.Packs.InfoTheory.Applications.ThermoRG as ThermoRGApp

import LogOS.Packs.InfoTheory.Core as InfoCore

private
  ShannonFacts_exists : _
  ShannonFacts_exists = InfoCore.ShannonFacts.ShannonFacts

  Carrier_exists : _
  Carrier_exists = InfoCore.ShannonFacts.Carrier

  LogSumIneq_exists : _
  LogSumIneq_exists = InfoCore.ShannonFacts.LogSumIneq

  DPIFacts_exists : _
  DPIFacts_exists = DPIApp.DPIFacts

  module _ (F : InfoCore.ShannonFacts.ShannonFacts) where
    module C = InfoCore.ShannonCore.For F

    Dist_exists : _
    Dist_exists = C.Dist

    Kernel_exists : _
    Kernel_exists = C.Kernel

    KL≥0_exists : _
    KL≥0_exists = C.KL≥0

  ObserverChannel_exists : _
  ObserverChannel_exists = InfoCore.ObserverDPI.ObserverChannel
```

Trust level: **stable** (but *axiom-pack driven*).

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

This note is the publication-facing entrypoint for the **information theory**
strand. LogOS does not attempt to rebuild real analysis; instead it packages
Shannon-style facts about a real-number model (`ShannonFacts`) as an explicit
record, and then derives the classical **interfaces** you actually use
downstream:

- **Data Processing Inequality (DPI)** as a theorem derived from a minimal extra axiom (`DPIFacts.klTerm-scale`).
- **Capacity** as an interface (definition of mutual information + a coding theorem boundary stated abstractly).
- **Thermo/RG bridge** as an interface (coarse-graining monotonicity + Landauer-style cost lower bounds).

The design is intentionally LogOS-like:
**you can swap the analytic model** (different `ShannonFacts`) without touching
the kernel, and you can connect the resulting inequalities to the complexity /
physics-of-information pipelines elsewhere in the repo.

Interpretation (analogy):
<!-- CLAIM-STAMP: ANALOGY | anchor=docs/Applications/InfoTheory.lagda.md#thermorg-label -->
`ThermoRG` uses “RG” as an interpretation label for coarse‑graining monotonicity.
The formal content lives in the explicit `RGFacts`/`LandauerShannonFacts` records.

Naming note (guardrail): `ThermoRG` is an abstract interface. The “RG” wording is
an interpretation (coarse‑graining monotonicity), not a claim that LogOS derives
renormalisation theory from first principles.

## Modeling style (facts packs)

The Shannon layer is expressed as an explicit record of *assumptions*:
`ShannonFacts` is not “the real numbers”, but an abstract carrier `ℝ` equipped
with the minimum structure the finite theorems in this pack actually use:

- Operations (`0#`, `1#`, `_+_`, `_*_`, `-_`) and the one unit law used by the derived theorems (`*-idr`).
- An order (`_≤_`) and enough finite-sum structure (`sum`, monotonicity, swap).
- A positivity predicate `Pos`.
- A total “KL term” `klTerm`, together with the explicit nonnegative zero-case law
  assumed by this library (`klTerm0≤ : 0 ≤ b → klTerm 0 b = 0`).
- The log-sum inequality `logSumIneq` as the single heavy analytic ingredient.
<!-- CLAIM-STAMP: LITERAL | anchor=LogOS/InfoTheory/Shannon/Facts.agda#ShannonFacts -->

This keeps the library honest: if you change the analytic model, you do so by
changing a record value, not by rewriting proofs.

## What is proved (and what is only assumed)

Within `ShannonCore` (parameterized by `ShannonFacts`) LogOS defines the usual
finite objects (`Dist`, `Kernel`, pushforwards) and proves the first “real”
lemma most downstream uses want:

- `KL≥0` (Gibbs’ inequality / nonnegativity of KL) derived from `logSumIneq`.
<!-- CLAIM-STAMP: LITERAL | anchor=LogOS/Packs/InfoTheory/Core.agda#ShannonCore.For.KL≥0 -->

Everything beyond that is packaged as a small number of additional assumption records:

- DPI: `DPIFacts` adds just one extra law (`klTerm-scale`), and then derives the finite KL DPI.
- Capacity: `CapacityFacts` is an interface (mutual information is defined here; achievability/converse are abstract).
- Thermo/RG: `RGFacts` + `LandauerShannonFacts` are interfaces connecting coarse‑graining entropy increase to an abstract cost lower bound.

## Connection back to LogOS (observer/semantics view)

`LogOS.InfoTheory.ObserverDPI` rephrases “DPI” as a purely order‑theoretic
statement: an observer/channel is a `run : Obs → Obs` that is nonincreasing for
an information preorder. This is a clean bridge point if you want to feed
Shannon-style monotonicity statements into other LogOS stories without importing
analytic detail into the kernel.
<!-- CLAIM-STAMP: REPRESENTATIONAL | anchor=LogOS/InfoTheory/ObserverDPI.agda#ObserverChannel -->

## Where to look

- Curated pack surface: `LogOS/Packs/InfoTheory/All.agda`
- Stable lock surface: `LogOS/Packs/InfoTheory/Surface.agda`
- Minimal stable surface: `LogOS/Packs/InfoTheory/Core.agda`
- Application wrappers (quartets): `LogOS/Packs/InfoTheory/Applications/All.agda`

## The three application entrypoints

- DPI (derived theorem): `LogOS/Packs/InfoTheory/Applications/DPI.agda`
  - Facts pack: `DPIApp.DPIFacts`
  - Quartet wrapper: `DPIApp.Pack` / `DPIApp.mkPack`
- Capacity (interface): `LogOS/Packs/InfoTheory/Applications/Capacity.agda`
  - Math-facing layer: `CapApp.For` (defines `I` and `CapacityFacts`)
  - Quartet wrapper: `CapApp.Pack` / `CapApp.mkPack`
- Thermo/RG bridge (interface): `LogOS/Packs/InfoTheory/Applications/ThermoRG.agda`
  - Math-facing layer: `ThermoRGApp.For` (defines `RGFacts` and `LandauerShannonFacts`)
  - Quartet wrapper: `ThermoRGApp.Pack` / `ThermoRGApp.mkPack`

## Curated import (namespaced)

```text
open import LogOS.Packs.InfoTheory.Surface as IT
open import LogOS.Packs.InfoTheory.Applications.All as ITApp
module DPI      = ITApp.DPI
module Capacity = ITApp.Capacity
module ThermoRG = ITApp.ThermoRG
```
