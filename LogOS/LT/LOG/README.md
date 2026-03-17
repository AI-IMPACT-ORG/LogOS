<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS.LT.LOG

2-categorical packaging of the LT architecture.

- `Kernel2Cat.agda`: preserved observational comparison world
- `Boundary2Cat.agda`: architecture-first displayed packaging
- `Implementation2Cat.agda`, `ImplementationContract2Cat.agda`,
  `ImplementationFlow2Cat.agda`, `ImplementationDecode2Cat.agda`:
  implementation, contract, flow, and decode layers
- `QuotePort2Cat/**`, `EncodePort2Cat/**`: quotation and encoding surfaces
- `Discipline/**`: policy-facing witnesses that ports stay displayed and totalised

Use `LogOS/API/Kernel.agda` or `LogOS/API/Architecture.agda` for curated public
entrypoints into this lane.
