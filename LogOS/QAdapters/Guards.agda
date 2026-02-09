{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.Guards where

-- Non-vacuity witnesses for prequantale/time adapters: the scale is not collapsed.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Minimal.Adapter using (QAdapter)

record QAdapterVacuityGuards {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  open QAdapter Q
  field
    unit-not-bottom : ¬ (e ≡ ⊥s)
