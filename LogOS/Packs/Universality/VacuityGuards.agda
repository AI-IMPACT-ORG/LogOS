{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.VacuityGuards where

-- Non-vacuity guard: the core stepper is not a global fixed point.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Domain.Universality.Core using (CoreUCode; stepCoreU)

record CoreStepperNontrivial : Set where
  field
    witness  : CoreUCode
    not-fixed : ¬ (stepCoreU witness ≡ witness)
