{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Definitional where

-- Definitional/bookkeeping equalities for the fuel-style universality base layer.

open import LogOS.Prelude
import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.TaskDefinitional as TaskDefinitional

open TaskDefinitional public

FuelObservationLaw
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
  → (fuel : CodeType → ℕ)
  → (runWithin : ℕ → CodeType → CodeType)
  → Set ℓCode
FuelObservationLaw fuel runWithin =
  ∀ budgetCode sourceCode →
    fuel (runWithin budgetCode sourceCode)
      ≡ Core.universalFuelAfter budgetCode (Core.active (fuel sourceCode))

mkFuelObservationLaw
  : ∀ {ℓCode : Level}
    {CodeType : Set ℓCode}
    {fuel : CodeType → ℕ}
    {runWithin : ℕ → CodeType → CodeType}
  → FuelObservationLaw fuel runWithin
  → FuelObservationLaw fuel runWithin
mkFuelObservationLaw observationLaw = observationLaw
