<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS.LT.Stack navigator

This subtree is the refinement-first stack surface.

- `Core.agda`: canonical stack-as-kernel definitions and same-boundary transport.
- `Builders.agda`: canonical constructors for stack maps and stack-kernel homs.
- `Laws.agda`: refinement-facing stack/program laws.
- `Program.agda`: boundary-endomorphism and program layer.
- `Extend.agda`: stack extension helpers.
- `Guarded.agda`: guarded stack constructions.
- `Definitional.agda`: bookkeeping equalities for stack packaging.
- `Strictification.agda`: explicit strict/equality collapse for stack surfaces.

Import guidance:

- use `LogOS/LT/Stack.agda` for the curated default surface;
- import `Definitional` or `Strictification` only when an explicit equality lane is required.
