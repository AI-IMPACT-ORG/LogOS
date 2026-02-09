<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Deep Dive — Documentation Notes

This folder contains “how it works” and “why it’s shaped this way” notes. Many
files are literate Agda and therefore typechecked by `make docs`.

Shared anchors:
- Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`
- Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`

Key entrypoints:
- Ports/adapters spine (hexagonal architecture): `docs/DeepDive/Architecture_PortsAdapters.lagda.md`
- Futamura × diagonal showcase walkthrough: `docs/DeepDive/FutamuraDiagonal_Showcase.lagda.md`
- PL mechanization spine (syntax/statics/dynamics): `docs/DeepDive/PLSpine.lagda.md`
  - Code spine used by the doc: `docs/DeepDive/PLSpineSpine.agda`
- Kernel implementer notes: `docs/DeepDive/IMPLEMENTING_KERNEL.md`
- Communication/boundary framing: `docs/DeepDive/Communication.lagda.md`
- Core science overview: `docs/DeepDive/CoreScience.lagda.md`
- Complexity deep dive (experimental): `docs/DeepDive/Complexity.lagda.md`
- ZFC demo: `docs/DeepDive/ZFC_Demo.lagda.md`
- AI-assisted modelling workflow: `docs/DeepDive/AIAssistedModeling.lagda.md`
- Research ideas and future work: `docs/DeepDive/IDEAS.md`
