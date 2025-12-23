<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Library Overview

```agda
module docs.Library where

-- Sync guard: the public surfaces this overview points at.
open import LogOS.API.Minimal
open import LogOS.Theorems.Core as Theorems
```

This is the landing “library overview” page for the generated HTML docs.

Where to start:
- Architecture + entrypoints: `docs/Definition.lagda.md`
- Research-grade record/law listing: `docs/Definition_Spec.lagda.md`

Stable import surfaces:
- Minimal kernel API: `LogOS/API/Minimal.agda`
- Curated core theorems: `LogOS/Theorems/Core.agda`

Major storylines:
- ZFC: `docs/Application_ZFC.lagda.md` (demo: `docs/DeepDive/ZFC_Demo.lagda.md`)
- Complexity: `docs/DeepDive/Complexity.lagda.md` (P vs NP note: `docs/Application_PvsNP.lagda.md`)
- Universality: `docs/Application_Universality.lagda.md`
- Opacity / GRH application: `docs/Application_Opacity.lagda.md`
