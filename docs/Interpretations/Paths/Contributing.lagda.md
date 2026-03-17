<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Path: contributing (how to extend without breaking philosophy)

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Paths.Contributing where

import LogOS.API.LT
```

Non-negotiables:

- Cold full gate (clean + telemetry + all lanes): `make check-all`
- Warm full gate (no clean + telemetry + all lanes): `make check-all-warm`
- AI/LLM hand-off gate: `make check-all`
- Default local lanes: `make check-policy`, `make check-core`, `make check-integration`, `make check-docs`, `make check-lib`
- Warm local lanes: `make check-core-warm`, `make check-integration-warm`, `make check-all-warm`
- Use `make check` only as a very fast API smoke test while iterating
- Keep layering intact: `docs/Core/Architecture/Diagram.lagda.md` + `scripts/check/layer_order_check.sh`
- Keep theorems placed correctly: `docs/Patterns/Content_Placement.lagda.md`
- Audit workflow (how to verify claims): `docs/Core/Orientation/Audit_Guide.lagda.md`
- If using an AI assistant, follow repo instructions: [AGENTS.md](../../../AGENTS.md)

Practical split:

- use warm lanes while iterating locally;
- use `make check-all` before hand-off when you need the cold umbrella gate.

Checklists:

- Add an app: `docs/Patterns/HowTo/HowTo_Add_App.lagda.md`
- Add a port: `docs/Patterns/HowTo/HowTo_Add_Port.lagda.md`
- Practical downstream architecture tips:
  `docs/Patterns/HowTo/HowTo_Practical_Architecture_Tips.lagda.md`
