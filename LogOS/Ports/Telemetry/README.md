<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
and to respect boundary observational equality (mutual refinement).

Program telemetry uses the observational preorder `ObsCospPreorder` (2-cells as
refinements); equivalence is mutual refinement.

Note: for boundary programs, “respects equivalence” is derivable from monotonicity
because `≈∂Cosp` is definitionally a pair of refinements; see
`programTelemetryPortFromMono` in `LogOS/Boundary/Telemetry.agda`.
