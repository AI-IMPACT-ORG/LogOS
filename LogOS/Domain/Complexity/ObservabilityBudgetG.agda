{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ObservabilityBudgetG where

open import LogOS.Prelude
open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Domain.Universality.MeasurementCapacity as MC
import LogOS.Domain.Complexity.ResourceSchemaG as RS

-- Grade-native Local Observability Budget (LOB) interface.
-- Bounds live in the grade; ℕ only appears for sizes and counted events.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Q     : QAdapter ℓQ)
           where

  open QAdapter Q renaming (_≤s_ to _≤g_)

  module S = RS.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Q

  record LOB : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      κ    : ℕ
      need : Input → ℕ

      -- Capacity: any correct algorithm must spend enough non-unitary events.
      need≤κ·meas : ∀ {L} (QD : S.QTimeDeciderG L) (x : Input) →
                      need x ≤ℕ MC.mul κ (S.QTimeDeciderG.meas QD x)

      -- Throughput: non-unitary events are time-bounded (by grade).
      budget : QAdapter.Scale Q → ℕ
      monoBudget : ∀ {t u} → _≤g_ t u → budget t ≤ℕ budget u
      meas≤budget : ∀ {L} (QD : S.QTimeDeciderG L) (x : Input) →
                      S.QTimeDeciderG.meas QD x ≤ℕ budget (S.QTimeDeciderG.time QD x)

  toCapacity : LOB → S.CapacityG
  toCapacity lob =
    record
      { κ = LOB.κ lob
      ; info = LOB.need lob
      ; info≤κ·meas = LOB.need≤κ·meas lob
      }

  toThroughput : LOB → S.ThroughputG
  toThroughput lob =
    record
      { budget = LOB.budget lob
      ; monoBudget = LOB.monoBudget lob
      ; meas≤budget = LOB.meas≤budget lob
      }
