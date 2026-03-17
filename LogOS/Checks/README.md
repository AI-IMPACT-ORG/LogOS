<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS.Checks

Policy-only typecheck roots and theorem witness bundles.

- `Reachability/*.agda`: non-public roots used by repository policy
- `Conventions/*.agda`: tiny executable doctrine witnesses for high-risk semantic conventions
- theorem witness files such as `ArchitecturalNormalForm.agda`,
  `ExtensionalReflection.agda`, and `FoundationalLogic.agda`

This lane is executable policy infrastructure, not part of the curated
downstream API surface.
