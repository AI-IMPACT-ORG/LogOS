{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ResourceSchemaG where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.NatOrder using (_≤ℕ_; trans≤ℕ)

open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Domain.Universality.MeasurementCapacity as MC

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
