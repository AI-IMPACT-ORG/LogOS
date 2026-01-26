{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.Guards where

-- Non-vacuity witnesses for quantale/time adapters: the scale is not collapsed.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Minimal.Adapter using (QAdapter)

record QAdapterVacuityGuards {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  open QAdapter Q
  field
    a             : Scale
    a-not-bottom  : ¬ (a ≡ ⊥s)
    unit-not-bottom : ¬ (e ≡ ⊥s)
