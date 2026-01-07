<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Architecture — Ports & Adapters (Canonical Spine)

```agda
{-# OPTIONS --safe #-}
module docs.Architecture_PortsAdapters where

-- Sync guard: the architecture spine this document explains.
import LogOS.API.Architecture as Arch
import LogOS.Boundary.Port
import LogOS.Ports.Semantic.All
import LogOS.Adapters.Views.All
```

This note makes the library’s **hexagonal architecture** explicit as a single
canonical spine.

The key claim is not “there are many modules”, but:

> if two external systems present the *same* boundary satisfaction relation, then
> the meaning‑preserving translation between them is **forced** (up to satisfaction),
> and closure/extension steps commute with that translation **provided** the chosen
> boundary endomap respects boundary observational equivalence (the explicit
> extensionality hypothesis in `ported-closure-naturality`).

A second, more “full‑metal modularity” claim is also supported:

> if two presentations live over *different* satisfaction relations connected by a
> satisfaction morphism (`SatMor`), then the canonical translation is again forced
> (up to satisfaction), and closure steps commute with translation once they are
> compatible with that morphism (the explicit compatibility hypothesis in the
> heterogeneous interlingua core).

An OO reading (without mutable state) is:
**OO reinterpreted through hexagonal architecture + category theory—objects as interface‑bearing semantic
points in a network, rather than stateful records with methods.**

- “Object” = a kernel instance (`LogOS/Kernel.agda`, `LogOS/Kernel/LogicKernel.agda`).
- “Interface/port” = boundary I/O + presentations (`LogOS/Boundary/IO.agda`, `LogOS/Boundary/Port.agda`).
- “Adapter” = canonical translation / view transport (`LogOS/Ports/Semantic/Interlingua.agda`, `LogOS/Kernel/Reindex.agda`).
- “Wiring” = categorical composition of processes (`LogOS/Computation/SchemeCategory.agda`).

## Layer 1: signatures + signature morphisms

- `LogOS/Base/Signature.agda`
- `LogOS/Base/Signature/Hom.agda`

## Layer 2: kernels + reindexing (views)

- `LogOS/Kernel.agda`
- `LogOS/Kernel/Reindex.agda`
- `LogOS/Kernel/HomOverSig.agda`

## Layer 3: boundary I/O (communicable meaning)

- `LogOS/Boundary/IO.agda`
- `LogOS/Boundary/MultiIO.agda`

Note: `BoundaryIO.to∂/from∂` are **program/context-level** wiring projections.
Do not confuse them with the **constraint-level** `ext`/`bnd` maps from the lax
adjunction (aka `Kernel.Holo`).

## Layer 4: boundary presentations (semantic ports)

Minimal port interface (export + import legs, with satisfaction equivalences):

- `LogOS/Boundary/Port.agda` (`BoundaryPort`)

Generic presentation interface over an arbitrary satisfaction relation:

- `LogOS/Ports/Semantic/InterlinguaCore.agda` (`PresentationC`)

## Layer 5: canonical interlingua (forced translation)

If two boundary presentations sit over the same boundary satisfaction relation,
the canonical translation is “route through the shared constraints”:

```text
Form₁  --Import₁-->  Con_bnd  --Interp₂-->  Form₂
```

This is implemented and proved in:

- `LogOS/Ports/Semantic/Interlingua.agda`

Theorems (names):
- `translate-preserves-Sat` (preserves and reflects satisfaction (`↔`) by construction)
- `translate-unique` (uniqueness up to satisfaction‑equivalence `Trans≈`/`≈⇒`)
- `ported-closure-naturality` (closure/extension commutes with translation, given `Respects≈∂[ B ]` for the closure map)

## Layer 5b: interoperability across changing logics

To compare *different* satisfaction relations, use:

- `LogOS/Ports/Semantic/SatMor.agda` (`SatMor`)
- `LogOS/Ports/Semantic/HeteroInterlinguaCore.agda` (canonical translation + uniqueness along `SatMor`)

`SatMor` is *defined* to be conservative: it preserves and reflects satisfaction
(it carries a `sat-↔`, with projections `sat→` / `sat←`).

Canonical `SatMor` instances induced by LogOS “views” live in:

- `LogOS/Adapters/Views/SatMor.agda`

## Layer 6: process/computation adapters (SchemeCategory)

For computation‑level comparison and transport (process morphisms, naturality of
budgeted execution, etc.):

- `LogOS/Computation/SchemeCategory.agda`

## Tooling: inputs/outputs (certificates)

To integrate *existing* provers/solvers (inputs = formulas, outputs = certificates),
use the generic `ProofSystem` interface and its pullback along canonical translations:

- `LogOS/Syntax/ProofSystem.agda` (`ProofSystem`)
- `LogOS/Ports/Semantic/ProofTransport.agda` (pull back provers/model-checkers along `translate` / `SatMor`)
  (includes helpers for the common “global validity / global model-checker” shape).

For a compact “external logic system” wrapper (presentation + prover/solver I/O), see:

- `LogOS/Ports/Semantic/SystemIO.agda` (`SystemIO`, `rebase`, `rebaseAlongSatMor`)
  (`rebaseAlongSatMor` pulls back both prover + model-checker; the model-checker transport is canonical via `mapCtx`).

## Canonical import map

If you want this exact spine as a curated import surface, use:

- `LogOS/API/Architecture.agda`
