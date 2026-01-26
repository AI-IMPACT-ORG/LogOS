{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ResourceSchemaG where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; to; from)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude.Sum using (_⊎_)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Computation.Decider using (Decider)
import LogOS.Domain.Complexity.MeasurementCapacity as MC

-- Grade-native resource schema (no ℕ-polynomial scaffolding).
-- Bounds live in the grade; size is only used as an index.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Q     : QAdapter ℓQ)
           where

  open QAdapter Q renaming (Scale to Grade; _≤s_ to _≤g_)

  Language : Set (ℓI ⊔ lsuc ℓ)
  Language = Input → Set ℓ

  record QTimeDeciderG (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      decide : Input → Set ℓ
      total  : ∀ x → decide x ⊎ ¬ decide x
      sound  : ∀ x → decide x → L x
      comp   : ∀ x → L x → decide x

      time : Input → Grade
      meas : Input → ℕ

      boundG : ℕ → Grade
      time≤G : ∀ x → _≤g_ (time x) (boundG (size x))

  -- Forget the resource fields: any `QTimeDeciderG` is a total decider.
  toDeciderG : ∀ {L} → QTimeDeciderG L → Decider Input L
  toDeciderG qd =
    record
      { decide = QTimeDeciderG.decide qd
      ; total  = QTimeDeciderG.total qd
      ; sound  = QTimeDeciderG.sound qd
      ; comp   = QTimeDeciderG.comp qd
      }

  -- Transport a grade-native time decider across pointwise logical equivalence.
  -- This keeps time/measurement/bounds unchanged.

  mapQTimeDeciderG
    : ∀ {L L′}
      → (∀ x → L x ↔ L′ x)
      → QTimeDeciderG L
      → QTimeDeciderG L′
  mapQTimeDeciderG eq qd =
    record
      { decide = QTimeDeciderG.decide qd
      ; total  = QTimeDeciderG.total qd
      ; sound  = λ x dx → to (eq x) (QTimeDeciderG.sound qd x dx)
      ; comp   = λ x lx → QTimeDeciderG.comp qd x (from (eq x) lx)
      ; time   = QTimeDeciderG.time qd
      ; meas   = QTimeDeciderG.meas qd
      ; boundG = QTimeDeciderG.boundG qd
      ; time≤G = QTimeDeciderG.time≤G qd
      }

  record ThroughputG : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      budget : Grade → ℕ
      monoBudget : ∀ {t u} → _≤g_ t u → budget t ≤ℕ budget u
      meas≤budget : ∀ {L} (QD : QTimeDeciderG L) (x : Input) →
                    QTimeDeciderG.meas QD x ≤ℕ budget (QTimeDeciderG.time QD x)

  record CapacityG : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      κ : ℕ
      info : Input → ℕ
      info≤κ·meas : ∀ {L} (QD : QTimeDeciderG L) (x : Input) →
                    info x ≤ℕ MC.mul κ (QTimeDeciderG.meas QD x)

  record HardG (L : Language) (TH : ThroughputG) (CP : CapacityG)
    : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ))) where
    field
      witness : ∀ (QD : QTimeDeciderG L) →
        Σ Input (λ x →
          let
            b = ThroughputG.budget TH (QTimeDeciderG.boundG QD (size x))
          in
          ¬ (CapacityG.info CP x ≤ℕ MC.mul (CapacityG.κ CP) b))

  notTimeBoundedG
    : ∀ {L} (TH : ThroughputG) (CP : CapacityG)
      → HardG L TH CP
      → ¬ (Σ (QTimeDeciderG L) (λ _ → ⊤ {ℓ = lzero}))
  notTimeBoundedG {L = L} TH CP H (qd , _) =
    let
      ex = HardG.witness H qd
      x  = proj₁ ex

      meas≤t : QTimeDeciderG.meas qd x ≤ℕ
               ThroughputG.budget TH (QTimeDeciderG.boundG qd (size x))
      meas≤t =
        trans≤ℕ
          (ThroughputG.meas≤budget TH qd x)
          (ThroughputG.monoBudget TH (QTimeDeciderG.time≤G qd x))

      info≤κ·meas = CapacityG.info≤κ·meas CP qd x
    in
    proj₂ ex (trans≤ℕ info≤κ·meas (MC.monoMul (CapacityG.κ CP) meas≤t))

  -- Bounded deciders: restrict to a chosen bound class (e.g., PolyPredG).
  module Bounded {ℓB : Level} (IsBound : (ℕ → Grade) → Set ℓB) where

    record QTimeDecider (L : Language) : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ ⊔ ℓB))) where
      field
        decide : Input → Set ℓ
        total  : ∀ x → decide x ⊎ ¬ decide x
        sound  : ∀ x → decide x → L x
        comp   : ∀ x → L x → decide x

        time : Input → Grade
        meas : Input → ℕ

        boundG : ℕ → Grade
        boundOk : IsBound boundG
        time≤G : ∀ x → _≤g_ (time x) (boundG (size x))

    -- Forget the bound witness/resource fields.
    toDecider : ∀ {L} → QTimeDecider L → Decider Input L
    toDecider qd =
      record
        { decide = QTimeDecider.decide qd
        ; total  = QTimeDecider.total qd
        ; sound  = QTimeDecider.sound qd
          ; comp   = QTimeDecider.comp qd
          }

    -- Transport a bounded time decider across pointwise logical equivalence.
    -- This keeps time/measurement/bounds unchanged.

    mapQTimeDecider
      : ∀ {L L′}
        → (∀ x → L x ↔ L′ x)
        → QTimeDecider L
        → QTimeDecider L′
    mapQTimeDecider eq qd =
      record
        { decide  = QTimeDecider.decide qd
        ; total   = QTimeDecider.total qd
        ; sound   = λ x dx → to (eq x) (QTimeDecider.sound qd x dx)
        ; comp    = λ x lx → QTimeDecider.comp qd x (from (eq x) lx)
        ; time    = QTimeDecider.time qd
        ; meas    = QTimeDecider.meas qd
        ; boundG  = QTimeDecider.boundG qd
        ; boundOk = QTimeDecider.boundOk qd
        ; time≤G  = QTimeDecider.time≤G qd
        }

    toQTimeDeciderG : ∀ {L} → QTimeDecider L → QTimeDeciderG L
    toQTimeDeciderG qd =
      record
        { decide = QTimeDecider.decide qd
        ; total  = QTimeDecider.total qd
        ; sound  = QTimeDecider.sound qd
        ; comp   = QTimeDecider.comp qd
        ; time   = QTimeDecider.time qd
        ; meas   = QTimeDecider.meas qd
        ; boundG = QTimeDecider.boundG qd
        ; time≤G = QTimeDecider.time≤G qd
        }

    record Hard (L : Language) (TH : ThroughputG) (CP : CapacityG)
      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓQ ⊔ ℓB))) where
      field
        witness : ∀ (QD : QTimeDecider L) →
          Σ Input (λ x →
            let
              b = ThroughputG.budget TH (QTimeDecider.boundG QD (size x))
            in
            ¬ (CapacityG.info CP x ≤ℕ MC.mul (CapacityG.κ CP) b))

    notTimeBounded
      : ∀ {L} (TH : ThroughputG) (CP : CapacityG)
        → Hard L TH CP
        → ¬ (Σ (QTimeDecider L) (λ _ → ⊤ {ℓ = lzero}))
    notTimeBounded {L = L} TH CP H (qd , _) =
      let
        ex = Hard.witness H qd
        x  = proj₁ ex

        qdG = toQTimeDeciderG qd

        meas≤t : QTimeDeciderG.meas qdG x ≤ℕ
                 ThroughputG.budget TH (QTimeDeciderG.boundG qdG (size x))
        meas≤t =
          trans≤ℕ
            (ThroughputG.meas≤budget TH qdG x)
            (ThroughputG.monoBudget TH (QTimeDeciderG.time≤G qdG x))

        info≤κ·meas = CapacityG.info≤κ·meas CP qdG x
      in
      proj₂ ex (trans≤ℕ info≤κ·meas (MC.monoMul (CapacityG.κ CP) meas≤t))
