{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.ObservabilityBudgetGraded where

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Complexity.Poly using (PolyPred)
import LogOS.Complexity.ObservabilityBudgetG as OBG

-- Grade-native Local Observability Budget (LOB) interface.
-- Time bounds are grades; ℕ only appears for sizes and counted events.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (_Pℕ   : PolyPred)
           (Q     : QAdapter ℓQ)
           (_gradeBound : ℕ → QAdapter.Scale Q)
           where

  module G = OBG.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Q

  -- The LOB interface is independent of the chosen bound class.
  -- This module keeps the “graded” name, but re-exports the grade-native LOB pack.
  open G public renaming (LOB to LOBG; toCapacity to toCapacityG; toThroughput to toThroughputG)

  LOB = LOBG
  toCapacity = toCapacityG
  toThroughput = toThroughputG
