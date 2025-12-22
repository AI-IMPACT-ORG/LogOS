{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ObservabilityBudgetGraded where

open import LogOS.Prelude
open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.ResourceSchemaGraded as RS
import LogOS.Domain.Complexity.ObservabilityBudgetG as OBG
import LogOS.Domain.Universality.MeasurementCapacity as MC

-- Grade-native Local Observability Budget (LOB) interface.
-- Time bounds are grades; ℕ only appears for sizes and counted events.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
           (gradeBound : ℕ → QAdapter.Scale Q)
           where

  module R = RS.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Pℕ Q gradeBound
  module G = OBG.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Q
  open G public renaming (LOB to LOBG; toCapacity to toCapacityG; toThroughput to toThroughputG)

  record LOB : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      κ    : ℕ
      need : Input → ℕ

      -- Capacity: any correct algorithm must spend enough non-unitary events.
      need≤κ·meas : ∀ {L} (QD : R.QTimeDecider L) (x : Input) →
                      need x ≤ℕ MC.mul κ (R.QTimeDecider.meas QD x)

      -- Throughput: non-unitary events are time-bounded (by grade).
      budget : R.Grade → ℕ
      monoBudget : ∀ {t u} → QAdapter._≤s_ Q t u → budget t ≤ℕ budget u
      meas≤budget : ∀ {L} (QD : R.QTimeDecider L) (x : Input) →
                      R.QTimeDecider.meas QD x ≤ℕ budget (R.QTimeDecider.time QD x)

  toCapacity : LOB → R.Capacity
  toCapacity lob =
    record
      { κ = LOB.κ lob
      ; info = LOB.need lob
      ; info≤κ·meas = LOB.need≤κ·meas lob
      }

  toThroughput : LOB → R.Throughput
  toThroughput lob =
    record
      { budget = LOB.budget lob
      ; monoBudget = LOB.monoBudget lob
      ; meas≤budget = LOB.meas≤budget lob
      }
