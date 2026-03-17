<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Weak vs strict KernelHom

`KernelHom` is weak by design. This page shows the opt-in path to strictness.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Clarifications.Weak_vs_Strict_KernelHom where

import LogOS.API.LT
```

Default:

- `KernelHom = KernelHom≈`
- `decode-mapCode≈` is the intended public coherence law

Explicit strictification:

- `KernelHom≡` lives only under `LogOS.API.Strictification.Kernel`
- `Ports.ClassicalLimit` collapses `≈` to `≡` from an antisymmetry assumption
- `Globalise` is a separate extensional/global collapse step, not part of the default kernel API

Minimal weak reading:

- keep the adapter as `KernelHom`
- reason with `_⇒∂_`, `decode-mapCode≈`, and `ObservedCodePreorder`

Minimal strict reading:

- supply antisymmetry explicitly
- strictify with `Ports.ClassicalLimit.strictifyKernelHom`
- only then reason in `≡`
