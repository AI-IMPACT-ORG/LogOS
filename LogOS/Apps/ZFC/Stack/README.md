<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# ZFC Stack

Reusable stack-level packaging for the ZFC app.

- `ProfileTower/Core.agda`, `Boundary.agda`: shared boundary and stack setup
- `ZFCore/**`: base stack ingredients
- `AsymptoticReification/**`: staged reification and hierarchy tower machinery
- `WellFoundedPart/**`: well-founded restriction layer

This directory is the reusable layer beneath the concrete iterative-tree model.
