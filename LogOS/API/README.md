<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS.API

Curated public entrypoints for downstream users.

- `LT.agda`: default logical-transformer surface
- `Architecture.agda`: typed tetrahedron/face surface (also re-exported by `LT.agda`)
- `Minimal.agda`: smallest stable onboarding surface
- `Kernel.agda`: architecture / implementation / facade split
- `Ports.agda`: default boundary-interface surface
- `Guarded.agda`, `Strictification.agda`: explicit opt-in companions

Boundary rule:

- `LogOS/API/**` is for conceptual public surfaces only.
- Policy-only reachability roots live under `LogOS/Checks/Reachability/**`.
