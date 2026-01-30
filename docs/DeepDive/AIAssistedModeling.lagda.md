<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% AI-Assisted Axiomatic Modelling (Model-of-Models)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.AIAssistedModeling where

open import LogOS.API.Architecture as Architecture
open Architecture.Downstream
open import LogOS.Theorems.Core as Theorems
```

LogOS is designed for AI-assisted axiomatic modelling:

- **Assistants propose** definitions, axiom packs, and translation layers.
- **Agda checks** the resulting obligations (type correctness / proofs).
- **CI policies check** architectural constraints (host surfaces, import layers,
  postulate policies) so that semantic boundaries do not silently collapse.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

In this sense, LogOS is a *model-of-models*: it standardises how a “model” is
packaged as explicit assumptions + a protected kernel interface + swappable
semantic adapters + auditable translations.

Pointers used by the Nature-facing narrative:
- Communication pipeline: `docs/DeepDive/Communication.lagda.md`
- Core science results: `docs/Library.lagda.md`
