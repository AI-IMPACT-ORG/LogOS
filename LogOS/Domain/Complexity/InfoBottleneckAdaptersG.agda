{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.InfoBottleneckAdaptersG where

open import LogOS.Prelude
open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Domain.Universality.MeasurementCapacity as MC
import LogOS.Domain.Complexity.InfoHardnessBridge as IHB
import LogOS.Domain.Complexity.ResourceSchemaG as RS
import LogOS.Domain.Complexity.ObservabilityBudgetG as OB

-- Grade-native adapters: LOB packs + DetWithinAt give DetBottleneck.

module FromLOB
  {ℓI ℓD ℓQ ℓPG : Level}
  (Input : Set ℓI)
  (Size : Input → ℕ)
  (Q : QAdapter ℓQ)
  (IsPolyG : (ℕ → QAdapter.Scale Q) → Set ℓPG)
  (DetWithinAt : QAdapter.Scale Q → Input → Set ℓD)
  where

  open QAdapter Q renaming (_≤s_ to _≤g_; Scale to Grade)

  module G = IHB.GenericGradePoly Input Size Grade IsPolyG DetWithinAt
  open G public using (DetBottleneck)

  module R = RS.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Q
  module O = OB.For {ℓI = ℓI} {ℓ = ℓD} {ℓQ = ℓQ} Input Size Q

  record DetRunAsQTimeG : Set (lsuc (lsuc (ℓI ⊔ ℓD ⊔ ℓQ))) where
    field
      L  : R.Language
      QD : R.QTimeDeciderG L
      time≤ : ∀ {g} (x : Input) →
              DetWithinAt g x → _≤g_ (R.QTimeDeciderG.time QD x) g

  detBottleneck : (lob : O.LOB) → DetRunAsQTimeG → DetBottleneck
  detBottleneck lob dr =
    record
      { κ      = O.LOB.κ lob
      ; need   = O.LOB.need lob
      ; budget = O.LOB.budget lob
      ; detNeed≤budget =
          λ {g} x within →
            let
              open DetRunAsQTimeG dr
              need≤κ·meas = O.LOB.need≤κ·meas lob QD x
              meas≤budget-time = O.LOB.meas≤budget lob QD x
              meas≤budget-g =
                trans≤ℕ
                  meas≤budget-time
                  (O.LOB.monoBudget lob (time≤ x within))
            in
            trans≤ℕ need≤κ·meas (MC.monoMul (O.LOB.κ lob) meas≤budget-g)
      }
