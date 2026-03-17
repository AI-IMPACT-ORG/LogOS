<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Path: systems / architecture (ports → adapters → apps)

Goal: read LogOS as a hexagonal architecture where semantics is an explicit boundary and adapters are certified
wiring.

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Paths.Systems where

import LogOS.API.LT
```

1) Start here
-------------

- Layering + import discipline: `docs/Core/Architecture/Diagram.lagda.md`
- Ports directory (interfaces): `LogOS/API/Ports.agda` (curated surfaces; implementations live under `LogOS/Ports/**`)
- Content placement policy: `docs/Patterns/Content_Placement.lagda.md`

2) One “tooling loop” to internalise
------------------------------------

- Flow transport (normalisation commutes with translation up to refinement):
  `LogOS/LT/Theorems/Effectivisation.agda` (`normalize-decode-mapCode`)
- Stable completion (reify effective/stable semantics as code, closure-gated):
  `LogOS/LT/Theorems/StableCompletion.agda` (`stableCompletion-law`)

3) Optional observability buses
-------------------------------

- I/O ports (admissible inputs + output/telemetry as observations): `LogOS/Ports/IO.agda`
- Budget/valuation surface (explicit numerics, no kernel change): `LogOS/API/Valuation.agda`
- Completeness as an explicit boundary interface (iteration summaries/fixed point spines): `LogOS/LT/Sup/`
