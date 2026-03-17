<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS.Ports.Valuation

Quantitative adapter and valuation-algebra lane.

- `QAdapter.agda`, `NatQAdapter.agda`, and
  `QAdapterBudgetTransport.agda`: time/budget adapters and transports
- `ScaleBoundary.agda`: scale-sensitive boundary packaging
- optional algebraic layers such as regularisation, nuclei, and dimensions

Use `LogOS/API/Ports/Valuation.agda` for the default curated surface and
`LogOS/API/Valuation.agda` for the broader optional algebra view.
