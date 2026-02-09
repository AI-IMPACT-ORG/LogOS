{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Guards.ObserverCore where

open import LogOS.Prelude

open import LogOS.Theorems.Meta.Guards
open import LogOS.Theorems.Meta.ObserverCore as ObsCore

-- `NonVacuousObserver` implies simple nontriviality of the chosen truth predicate.

nontrivialTruthK
  : ∀ {ℓCode ℓDec ℓT : Level}
    {Code : Set ℓCode} {Dec : Set ℓDec}
    {decode : Code → Dec}
    {TruthK : Code → Set ℓT}
  → ObsCore.NonVacuousObserver Code Dec decode TruthK
  → NontrivialPred Code TruthK
nontrivialTruthK NV =
  record
    { trueWitness  = ObsCore.NonVacuousObserver.trueWitness NV
    ; falseWitness = ObsCore.NonVacuousObserver.falseWitness NV
    }
