<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Packs

```agda
module docs.Packs where

-- Sync guard: curated pack bundles should keep type-checking.
open import LogOS.Packs.ZFC.All as ZFC
open import LogOS.Packs.Universality.All as Universality
```

This page lists the curated “publication bundles” under `LogOS/Packs/*`.

- ZFC bundle: `LogOS/Packs/ZFC/All.agda`
  - Recommended surface: `LogOS/Packs/ZFC/All.agda` (pack-first; see `ZFC.WFGraph.*`)
  - Narrative: `docs/Application_ZFC.lagda.md`

- Universality bundle: `LogOS/Packs/Universality/All.agda`
  - Recommended surfaces: `LogOS/Models/Universality/Core.agda`, `LogOS/Models/UniversalIR/Core.agda`
  - Narrative: `docs/Application_Universality.lagda.md`
