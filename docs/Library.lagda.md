<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Library Overview

```agda
{-# OPTIONS --safe #-}
module docs.Library where

-- Sync guard: the public surfaces this overview points at.
open import LogOS.API.Minimal
open import LogOS.Theorems.Core as Theorems

-- Curated pack bundles (kept typecheckable in CI).
open import LogOS.Packs.ZFC.Surface as ZFC
open import LogOS.Packs.Universality.Surface as Universality
open import LogOS.Packs.UniversalIR.Surface as UniversalIR
open import LogOS.Packs.Opacity.Surface as Opacity
open import LogOS.Packs.Complexity.Surface as Complexity
open import LogOS.Packs.InfoTheory.Surface as InfoTheory
open import LogOS.Packs.Agents.Surface as Agents
import LogOS.MetaLanguage.All

-- Core science “headline” surfaces (small and stable).
import LogOS.Packs.Complexity.PhysicsOfInformation as POI
import LogOS.Packs.UniversalIR.Agreement as UAgree
```

This is the landing “library overview” page for the generated HTML docs.

Where to start:
- Architecture + entrypoints: `docs/Definition.lagda.md`
- Ports/adapters spine: `docs/Architecture_PortsAdapters.lagda.md`
- Research-grade record/law listing: `docs/Definition_Spec.lagda.md`
- Communication view (boundary/channel framing): `docs/DeepDive/Communication.lagda.md`
- AI-assisted modelling workflow: `docs/DeepDive/AIAssistedModeling.lagda.md`
- Kernel views (same core, different readings):
  - Multi-institution: `docs/View_MultiInstitution.lagda.md`
  - 3+ level HoTT-style: `docs/View_HoTT_3Level.lagda.md`
  - 2-category logic: `docs/View_CategoricalLogic.lagda.md`
  - Observer semantics: `docs/View_ObserverSemantics.lagda.md`

Stable import surfaces:
- Minimal kernel API: `LogOS/API/Minimal.agda`
- Curated core theorems: `LogOS/Theorems/Core.agda`

Major storylines (docs-first entrypoints):
- ZFC: `docs/Application_ZFC.lagda.md` (demo: `docs/DeepDive/ZFC_Demo.lagda.md`)
- Complexity: `docs/DeepDive/Complexity.lagda.md` (application note: `docs/Application_Complexity.lagda.md`)
- Universality / UniversalIR: `docs/Application_Universality.lagda.md`
- Opacity / observability: `docs/Application_Opacity.lagda.md`
- Agents (socket + monitoring/auditing): `docs/Application_Agents.lagda.md`

Curated packs (code-first entrypoints):
- ZFC bundle: `LogOS/Packs/ZFC/All.agda` (WFGraph quartets: `LogOS/Packs/ZFC/WFGraph.agda`)
- Universality bundle: `LogOS/Packs/Universality/All.agda` (UniversalIR-first bundle)
- UniversalIR bundle: `LogOS/Packs/UniversalIR/All.agda`
- Opacity bundle: `LogOS/Packs/Opacity/All.agda`
- Complexity bundle: `LogOS/Packs/Complexity/All.agda`
- Information theory bundle: `LogOS/Packs/InfoTheory/All.agda`
- Agents bundle: `LogOS/Packs/Agents/All.agda`

## Core science (checked)

Two small, “headline” results used by the public narrative are kept stable and
typechecked in CI.

```agda
open POI public

merge-implies-entropy-increase' : _
merge-implies-entropy-increase' = merge-implies-entropy-increase

irreversible-io-cost-lower-bound' : _
irreversible-io-cost-lower-bound' = irreversible-io-cost-lower-bound

open UAgree public
```
