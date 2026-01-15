<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Library Overview

```agda
{-# OPTIONS --safe #-}
module docs.Library where

-- Core science “headline” surfaces (small, checked, still experimental).
import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation as POI
import LogOS.Packs.UniversalIR.Agreement as UAgree
```

This is the landing “library overview” page for the generated HTML docs.

Trust note: each pack surface exposes `packTrust`
(`LogOS/Packs/Trust.agda`) to mark stable vs experimental status.

Where to start:
- Architecture + entrypoints: `docs/Definition.lagda.md`
- Ports/adapters spine: `docs/Architecture_PortsAdapters.lagda.md`
- Research-grade record/law listing: `docs/Definition_Spec.lagda.md`
- Communication view (boundary/channel framing): `docs/DeepDive/Communication.lagda.md`
- AI-assisted modelling workflow: `docs/DeepDive/AIAssistedModeling.lagda.md`
- Kernel views (same core, different readings):
  - Multi-institution: `docs/Views/MultiInstitution.lagda.md`
  - 3-level HoTT-style: `docs/Views/HoTT_3Level.lagda.md`
  - Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
  - Observer semantics: `docs/Views/ObserverSemantics.lagda.md`
  - CHL capstone: `docs/Views/CurryHowardLambek.lagda.md`

Stable import surfaces:
- Minimal kernel API: `LogOS/API/Minimal.agda`
- Curated core theorems: `LogOS/Theorems/Core.agda`

Major storylines (docs-first entrypoints):
- ZFC: `docs/Applications/ZFC.lagda.md` (demo: `docs/DeepDive/ZFC_Demo.lagda.md`)
- Complexity (experimental): `docs/DeepDive/Complexity.lagda.md` (application note: `docs/Applications/Complexity.lagda.md`)
- Universality / UniversalIR: `docs/Applications/Universality.lagda.md`
- Opacity / observability (experimental): `docs/Applications/Opacity.lagda.md`
- Agents (socket + monitoring/auditing): `docs/Applications/Agents.lagda.md`

Curated packs (code-first entrypoints):
- ZFC bundle: `LogOS/Packs/ZFC/All.agda` (WFGraph quartets: `LogOS/Packs/ZFC/WFGraph.agda`)
- Universality bundle: `LogOS/Packs/Universality/All.agda` (UniversalIR-first bundle)
- UniversalIR bundle: `LogOS/Packs/UniversalIR/All.agda`
- Opacity bundle (experimental): `LogOS/Packs/Opacity/Experimental/All.agda`
- Complexity bundle (experimental): `LogOS/Packs/Complexity/Experimental/All.agda`
- Information theory bundle: `LogOS/Packs/InfoTheory/All.agda`
- Agents bundle (stable): `LogOS/Packs/Agents/All.agda`
- Agents experimental extensions: `LogOS/Packs/Agents/Experimental/All.agda`

## Core science (checked)

Two small, “headline” results used by the public narrative are typechecked in
CI, but they still live in experimental packs with explicit assumptions.

```agda
open POI public

merge-implies-entropy-increase' : _
merge-implies-entropy-increase' = merge-implies-entropy-increase

irreversible-io-cost-lower-bound' : _
irreversible-io-cost-lower-bound' = irreversible-io-cost-lower-bound

open UAgree public
```
