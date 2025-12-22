{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ResourceSchemaGraded where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Universality.MeasurementCapacity as MC
import LogOS.Domain.Complexity.ResourceSchemaG as RG

-- Grade-native resource schema: time/cost lives in the kernel grade,
-- while polynomial bounds remain ℕ-indexed and are lifted by `gradeBound`.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  Grade : Set ℓQ
  Grade = QAdapter.Scale Q

  infix 4 _≤g_
  _≤g_ : Grade → Grade → Set ℓQ
  _≤g_ = QAdapter._≤s_ Q

  module Base = RG.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Q
  open Base public using (Language; QTimeDeciderG; ThroughputG; CapacityG; HardG; notTimeBoundedG)

  -- Bounded deciders: expose a grade-valued time cost with an ℕ-polynomial bound.
  record QTimeDecider (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      decide : Input → Set ℓ
      total  : ∀ x → decide x ⊎ ¬ decide x
      sound  : ∀ x → decide x → L x
      comp   : ∀ x → L x → decide x

      time : Input → Grade
      meas : Input → ℕ

      boundT : ℕ → ℕ
      polyT  : PolyPred.isPoly Pℕ boundT
      time≤  : ∀ x → _≤g_ (time x) (gradeBound (boundT (size x)))

  toQTimeDeciderG : ∀ {L} → QTimeDecider L → QTimeDeciderG L
  toQTimeDeciderG qd =
    record
      { decide = QTimeDecider.decide qd
      ; total  = QTimeDecider.total qd
      ; sound  = QTimeDecider.sound qd
      ; comp   = QTimeDecider.comp qd
      ; time   = QTimeDecider.time qd
      ; meas   = QTimeDecider.meas qd
      ; boundG = λ n → gradeBound (QTimeDecider.boundT qd n)
      ; time≤G = QTimeDecider.time≤ qd
      }

  record Throughput : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      budget : Grade → ℕ
      monoBudget : ∀ {t u} → _≤g_ t u → budget t ≤ℕ budget u
      meas≤budget : ∀ {L} (QD : QTimeDecider L) (x : Input) →
                    QTimeDecider.meas QD x ≤ℕ budget (QTimeDecider.time QD x)

  record Capacity : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      κ : ℕ
      info : Input → ℕ
      info≤κ·meas : ∀ {L} (QD : QTimeDecider L) (x : Input) →
                    info x ≤ℕ MC.mul κ (QTimeDecider.meas QD x)

  record Hard (L : Language) (TH : Throughput) (CP : Capacity)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      witness : ∀ (QD : QTimeDecider L) →
        Σ Input (λ x →
          ¬ (Capacity.info CP x ≤ℕ
              MC.mul (Capacity.κ CP)
                (Throughput.budget TH (gradeBound (QTimeDecider.boundT QD (size x))))))

  notPolyTime
    : ∀ {L} (TH : Throughput) (CP : Capacity)
      → Hard L TH CP
      → ¬ (Σ (QTimeDecider L) (λ _ → ⊤ {ℓ = lzero}))
  notPolyTime {L = L} TH CP H (qd , _) =
    let
      ex = Hard.witness H qd
      x  = proj₁ ex

      meas≤t : QTimeDecider.meas qd x ≤ℕ
               Throughput.budget TH (gradeBound (QTimeDecider.boundT qd (size x)))
      meas≤t =
        trans≤ℕ
          (Throughput.meas≤budget TH qd x)
          (Throughput.monoBudget TH (QTimeDecider.time≤ qd x))

      info≤κ·meas = Capacity.info≤κ·meas CP qd x
    in
    proj₂ ex (trans≤ℕ info≤κ·meas (MC.monoMul (Capacity.κ CP) meas≤t))
