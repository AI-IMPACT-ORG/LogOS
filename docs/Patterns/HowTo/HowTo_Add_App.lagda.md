<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# How to add an application pack {#how-to-add-an-application-pack}

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.HowTo.HowTo_Add_App where

import LogOS.API.LT
```

1. Start by writing a **port** (interface) under `LogOS/Ports/**` that states:
   - what the boundary is (observations)
   - what counts as refinement
   - what assumptions are parameterised
   If the port must be functorial across kernel translations, prefer implementing it as a
   displayed layer over an explicit thin 2-category basis (see `LogOS/LT/DisplayedThin2Cat.agda` and `docs/Patterns/Ports_As_Displayed.lagda.md`).
   Basis guidance: internal ports/adapters should default to LOGᴳ; apps may use LOG explicitly
   when they are observational (e.g. physics/Deutsch).
2. Provide one or more **adapters** under `LogOS/Adapters/**` that implement the port.
3. Add a pack under `LogOS/Apps/` (e.g. `LogOS/Apps/Opacity/`) that:
   - composes ports/adapters
   - exports a small surface (ideally via `LogOS/API/**` once curated)
   - follows the content placement policy: `docs/Patterns/Content_Placement.lagda.md`
4. Keep the core minimal:
   - if it can be expressed as a translation/view/pullback, prefer that over adding new primitives.
5. If the pack needs **reification / self-reference**, import `LogOS.API.Reification` explicitly and use the restricted/staged/cross-stage port types in `LogOS/Ports/Reification/*`.
   - Default discipline: restricted reification + explicit admissibility witnesses.
   - Late-collapse discipline: stage-index admissibility (`StagedReification`) and derive the restricted surface by forgetting stages.
6. If the pack needs **strong assumptions**, encode them as explicit upgrade/ledger records so downstream users can audit axiom dependencies.
   Exemplar: `LogOS/Apps/ZFC/Stack/ProfileTower/Core.agda` (tower of explicit upgrades rather than silently bundled strength).
7. If the lower-rung machinery already exists, do not rederive it locally in the
   app. Use the practical guide:
   `docs/Patterns/HowTo/HowTo_Practical_Architecture_Tips.lagda.md`.
8. Start from one executable template whenever possible:
   - `LogOS/Checks/UniversalityAdapterTemplate.agda`
   - `LogOS/Checks/SmallLayeredSlice.agda`
