<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Deep Dive — Architecture — Ports & Adapters (Canonical Spine)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.Architecture_PortsAdapters where

-- Sync guard: the architecture spine this document explains.
import LogOS.API.Architecture as Arch
import LogOS.Boundary.Port as BPort
import LogOS.Ports.Semantic.All
import LogOS.Adapters.Views.All

import LogOS.Ports.Semantic.Interlingua as Interlingua
import LogOS.Ports.Semantic.Interoperability as Interoperability
import LogOS.Ports.Semantic.CanonicalPorts as CanonicalPorts
import LogOS.Theorems.Meta.Bootstrapping as Bootstrapping

private
  translate-preserves-Sat-exists : _
  translate-preserves-Sat-exists = Interlingua.translate-preserves-Sat

  translate-unique-exists : _
  translate-unique-exists = Interlingua.translate-unique

  ported-closure-naturality-exists : _
  ported-closure-naturality-exists = Interlingua.ported-closure-naturality

  ported-closure-naturality-ObsEndo-exists : _
  ported-closure-naturality-ObsEndo-exists = Interlingua.For.ported-closure-naturality-ObsEndo

  ObsEndo∂-exists : _
  ObsEndo∂-exists = BPort.ObsEndo∂

  adapter-respects-ObsEqF-exists : _
  adapter-respects-ObsEqF-exists = Interoperability.adapter-respects-ObsEqF

  composeAdapter-respects-ObsEqF-exists : _
  composeAdapter-respects-ObsEqF-exists = Interoperability.composeAdapter-respects-ObsEqF

  adapter-confluent-exists : _
  adapter-confluent-exists = Interoperability.For.adapter-confluent

  heteroCanonicalAdapter-exists : _
  heteroCanonicalAdapter-exists = Interoperability.heteroCanonicalAdapter

  heteroAdapter-unique-exists : _
  heteroAdapter-unique-exists = Interoperability.heteroAdapter-unique

  strictReindexAdapter-exists : _
  strictReindexAdapter-exists = Interoperability.strictReindexAdapter

  Box≡ExtendFlow-exists : _
  Box≡ExtendFlow-exists = CanonicalPorts.For.Box≡ExtendFlow

  bootstrap-iso-exists : _
  bootstrap-iso-exists = Bootstrapping.For.bootstrap-iso
```

This note makes the library’s **hexagonal architecture** explicit as a single
canonical spine.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

The key claim is not “there are many modules”, but:

> if two external systems present the *same* boundary satisfaction relation, then
> the translation between them is **forced** (unique up to satisfaction equivalence (↔)),
> and it preserves and reflects satisfaction (↔),
> and closure/extension steps commute with that translation **provided** the chosen
> boundary endomap respects boundary observational equality (the explicit
> extensionality hypothesis in `ported-closure-naturality`, which can be bundled as
> an `ObsEndo∂` witness).

A second, more “full‑metal modularity” claim is also supported:

> if two presentations live over *different* satisfaction relations connected by a
> satisfaction morphism (`SatMor`), then the canonical translation is again forced
> (up to satisfaction equivalence (↔)), and closure steps commute with translation once they are
> compatible with that morphism (the explicit compatibility hypothesis in the
> heterogeneous interlingua core).

Interpretation (analogy): an OO reading (without mutable state)
--------------------------------------------------------------
See `docs/DeepDive/Communication.lagda.md` for the OO analogy. This note stays
focused on the port/adapters spine and the precise (typed) translation/naturality claims.

## Layer 1: signatures + signature morphisms

- `LogOS/Base/Signature.agda`
- `LogOS/Base/Signature/Hom.agda`

## Layer 2: kernels + reindexing (views)

- `LogOS/Kernel.agda`
- `LogOS/Kernel/Reindex.agda`
- `LogOS/Kernel/HomOverSig.agda`
- Optional sentence-translation reindexing:
  `reindexKernelWithFml` / `reindexLogicKernelWithFml` (syntax view change; satisfaction is related by the `Sat*-precompose` lemmas).
- Canonical strict-syntax translation along reindexing:
  `LogOS/Ports/Semantic/InterlinguaStrictReindex.agda` (interlingua = `mapFml`).
- Canonical heterogeneous adapter across changing satisfactions:
  `LogOS/Ports/Semantic/Interoperability.agda` (`heteroCanonicalAdapter`, `heteroAdapter-unique`).
- Strict reindexing adapter (one-liner):
  `LogOS/Ports/Semantic/Interoperability.agda` (`strictReindexAdapter`).

## Layer 3: boundary I/O (communicable boundary constraints)

- `LogOS/Boundary/IO.agda`
- `LogOS/Boundary/MultiIO.agda`

Note: `BoundaryIO.to∂/from∂` are **program/context-level** wiring projections.
Do not confuse them with the **constraint-level** `ext`/`bnd` maps from the lax
adjunction (aka `Kernel.Holo`).

## Layer 4: boundary presentations (semantic ports)

Minimal port interface (export + import legs, with satisfaction equivalences (↔)):

- `LogOS/Boundary/Port.agda` (`BoundaryPort`)

Generic presentation interface over an arbitrary satisfaction relation:

- `LogOS/Ports/Semantic/InterlinguaCore.agda` (`PresentationC`)

## Layer 5: canonical interlingua (forced translation)

Rule of thumb: same satisfaction (`SatC`) ⇒ `Interlingua.translate`; different satisfactions ⇒ `SatMor` + heterogeneous interlingua (`HeteroInterlinguaCore`).

If two boundary presentations sit over the same boundary satisfaction relation,
the canonical translation is “route through the shared constraints”:

```text
Form₁  --Import₁-->  Con_bnd  --Interp₂-->  Form₂
```

This is implemented and proved in:

- `LogOS/Ports/Semantic/Interlingua.agda`

Theorems (names):
- `translate-preserves-Sat` (preserves and reflects satisfaction (`↔`) by construction)
- `translate-unique` (uniqueness up to satisfaction equivalence (↔), packaged as `Trans≈`/`≈⇒`)
- `ported-closure-naturality` (closure/extension commutes with translation, given `Respects≈∂[ B ]` for the closure map)
- `ported-closure-naturality-ObsEndo` (same, but takes a bundled `ObsEndo∂` endomap witness)

Note: `ported-closure-naturality` is a **one-step** statement about `Extend`. A
μ/limit-level naturality statement requires explicit ω‑sup/continuity structure.

In LogOS, the limit-level (Kleene `μ`) transport lives in the interoperability
spine:

- `LogOS/Ports/Semantic/Interoperability.agda` (`Limit.translate-μ≤`, `Limit.translate-μ≤↑`).

Both theorems package *all* required hypotheses as small records:

- `MuTransportData`: includes ωCPO structure + ω-continuous map, operator
  commutation, and (strong) monotonicity of the target satisfaction for all
  contexts.
- `MuTransportData↑`: same, but requires satisfaction monotonicity only at the
  contexts actually used by the transport (those of the form `mapCtx p`).

The reusable domain-theoretic engine is:

- `LogOS/Theorems/Boundary/MuFusion.agda` (`μ-fusion≤`).

Interoperability theorems (adapters between ports over a shared boundary satisfaction):
- `adapter-respects-ObsEqF` (ObsEqF transported by any adapter)
- `composeAdapter-respects-ObsEqF` (ObsEqF preserved by adapter composition)
- `adapter-confluent` (any two adapters between the same ports are `Adapter≈`-equivalent, i.e. pointwise satisfaction equivalence (↔))

These live in `LogOS/Ports/Semantic/Interoperability.agda` (not `LogOS/Ports/Semantic/Interlingua.agda`).

### Bootstrapping = canonical interlingua
The bootstrapping map is the **canonical** translation between two ports over the
same boundary satisfaction:

- `CodePort` (formulas are `Kernel.Code`; import is `decode`; export/`Interp` is `encode`)
- `BoundaryPort∂` (canonical port with `Form = Con_bnd`)
  Both are defined in `LogOS/Ports/Semantic/CanonicalPorts.agda`.

Kernel “box” closure is also port-level structure: `Box` is `BoundaryPort.Extend CodePort Flow`
(`Box≡ExtendFlow`).

This is not a separate compiler or transpiler: `bootstrap` is the interlingua
translation, and `unbootstrap` is the export back to code (`encode`). The
round‑trip facts are instances of `translate-comp` + `translate-id`. The
packaged adapter equivalence between these ports (`bootstrap-iso` as an `Adapter≈` witness) lives in
`LogOS/Theorems/Meta/Bootstrapping.agda`.

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
