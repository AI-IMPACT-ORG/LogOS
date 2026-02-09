<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Shannon pack (finite)
=====================

This directory isolates finite Shannon-theory statements behind a single facts pack:
`ShannonFacts` in `LogOS/InfoTheory/Shannon/Facts.agda`.

Interpretation (analogy):
labels like “RG flow” are motivational; theorems are exactly those derived from the `ShannonFacts` assumptions.

Definitions and derived theorems
- Distributions, kernels, entropy, KL, and `KL≥0`: `LogOS/InfoTheory/Shannon/Core.agda`
- Data processing inequality for KL (`KL-DPI`): `LogOS/InfoTheory/Shannon/DPI.agda`

Application-facing interfaces (axiomatized, model-instantiable)
- Capacity/coding theorem interface and a mutual-information expression: `LogOS/InfoTheory/Shannon/Capacity.agda`
- Coarse-graining (RG flow) + Landauer bridge scaffold: `LogOS/InfoTheory/Shannon/ThermoRG.agda`
