<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% High-risk conventions (LogOS v1.1)

This page exists to stop the common misreads.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Orientation.High_Risk_Conventions where

import LogOS.API.LT
```

- `_⊑_ c d` means `d` is stronger than `c`; when an order-flavoured public glyph helps, `c ≼ d` is the same refinement relation.
- `≈` is observational mutual refinement, not `≡`.
- `KernelHom` defaults to approximate coherence (`KernelHom≈`).
- `Flow` gives stabilisation/lax idempotence, not identity.
- `ObservedCodePreorder` is the pullback preorder induced by `decode`.
- Default LT/API surfaces are refinement-only; equality lives only in explicit `Strictification` and `Definitional` lanes.
- Strictification is opt-in (`LogOS.API.Strictification`, `Ports.ClassicalLimit`, `Globalise`).
- ZFC upgrades are explicit packaging boundaries, not ambient derivations.
