<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Information Theory (finite, facts-pack style)
============================================

This domain provides an information-theory layer in the same “facts-pack” style as
other LogOS application packs: analytic commitments (ℝ, ln/exp, inequalities) are
explicit fields of a record, and theorems are derived from those fields.

Interpretation (analogy):
terms like “RG” / “Landauer” in this domain are motivational labels; theorems are exactly those proved from the stated `ShannonFacts` fields.

Shannon (finite)
- Facts pack: `LogOS/Domain/InfoTheory/Shannon/Facts.agda`
- Core definitions + `KL≥0`: `LogOS/Domain/InfoTheory/Shannon/Core.agda`
- Data processing inequality (KL-DPI): `LogOS/Domain/InfoTheory/Shannon/DPI.agda`
- Capacity interface + mutual information: `LogOS/Domain/InfoTheory/Shannon/Capacity.agda`
- RG/Landauer bridge scaffold: `LogOS/Domain/InfoTheory/Shannon/ThermoRG.agda`

Curated surface
- Recommended stable import surface (no demos): `LogOS/Packs/InfoTheory/Core.agda`
