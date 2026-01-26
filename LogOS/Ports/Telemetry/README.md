<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Telemetry Ports

This folder defines telemetry port interfaces (no implementations).
Core definitions live in `LogOS/Boundary/Telemetry.agda` and are re-exported by
`LogOS/Ports/Telemetry/Core.agda`.

Telemetry ports expose observation-only hooks for:
- boundary constraints (`Con_bnd`)
- boundary programs (`∂Cosp` layer)

The trace domain is a full `ConPreorder`. Observations are required to be monotone
and to respect boundary observational equivalence.

Program telemetry uses the observational preorder `ObsCospPreorder` (2-cells as
refinements); equivalence is mutual refinement.
