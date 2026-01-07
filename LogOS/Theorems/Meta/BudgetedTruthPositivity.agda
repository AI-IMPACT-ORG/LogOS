{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.BudgetedTruthPositivity where

open import LogOS.Prelude

open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_; trans≤ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)

import LogOS.Theorems.Meta.TruthPositivity as TP

-- Budgeted/quantitative refinement of TruthPositivity:
-- “observable” becomes “observable within budget b”.
--
-- This is intended as the landing pad for:
-- - proof-length/certificate-budget observability,
-- - time-bounded Kolmogorov / Levin Kt observability,
-- - physical cost/throughput budgets.

record BudgetedTruthPositivity {ℓT ℓW ℓObs : Level}
  : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  field
    Test        : Set ℓT
    W-pos       : Test → Set ℓW
    Observable≤ : ℕ → Test → Set ℓObs
    monoObs     : ∀ {b b′ t} → b ≤ℕ b′ → Observable≤ b t → Observable≤ b′ t
    positivity≤ : ∀ b t → Observable≤ b t → W-pos t

  -- Unbudgeted observability (exists some finite budget).
  Observable : Test → Set (ℓObs ⊔ lzero)
  Observable t = Σ ℕ (λ b → Observable≤ b t)

  positivity : ∀ t → Observable t → W-pos t
  positivity t obs = positivity≤ (proj₁ obs) t (proj₂ obs)

-- Generalized form (graded-kernel friendly):
-- budgets live in an abstract carrier B with an order, rather than in ℕ.
--
-- This is the interface you want when budgets come from a quantale scale
-- (`QAdapter.Scale Q`) or other non-ℕ cost models.

record BudgetedTruthPositivityBy {ℓT ℓW ℓB ℓObs : Level}
  (B : Set ℓB)
  (_≤B_ : B → B → Set ℓObs)
  : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓB ⊔ ℓObs)) where
  field
    Test        : Set ℓT
    W-pos       : Test → Set ℓW
    Observable≤ : B → Test → Set ℓObs
    monoObs     : ∀ {b b′ t} → b ≤B b′ → Observable≤ b t → Observable≤ b′ t
    positivity≤ : ∀ b t → Observable≤ b t → W-pos t

-- A proof/certificate surface with an explicit budget/cost model.

record CostedProofWitness {ℓT ℓW ℓP : Level}
                          (Test  : Set ℓT)
                          (W-pos : Test → Set ℓW)
                          : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓP)) where
  field
    Proof : Test → Set ℓP
    check : ∀ {t} → Proof t → W-pos t
    cost  : ∀ {t} → Proof t → ℕ

fromCostedProofWitness
  : ∀ {ℓT ℓW ℓP}
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW : CostedProofWitness {ℓP = ℓP} Test W-pos)
  → BudgetedTruthPositivity {ℓT} {ℓW} {ℓP}
fromCostedProofWitness {Test = Test} {W-pos = W-pos} PW =
  record
    { Test        = Test
    ; W-pos       = W-pos
    ; Observable≤ = λ b t → Σ (CostedProofWitness.Proof PW t)
                           (λ p → CostedProofWitness.cost PW p ≤ℕ b)
    ; monoObs     = λ {b} {b′} {t} le (p , c≤) → p , trans≤ℕ c≤ le
    ; positivity≤ = λ b t obs → CostedProofWitness.check PW (proj₁ obs)
    }

record CostedProofWitnessBy {ℓT ℓW ℓB ℓP : Level}
                            (B : Set ℓB)
                            (_≤B_ : B → B → Set ℓP)
                            (Test  : Set ℓT)
                            (W-pos : Test → Set ℓW)
                            : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓB ⊔ ℓP)) where
  field
    Proof : Test → Set ℓP
    check : ∀ {t} → Proof t → W-pos t
    cost  : ∀ {t} → Proof t → B

fromCostedProofWitnessBy
  : ∀ {ℓT ℓW ℓB ℓP}
    {B : Set ℓB}
    (≤B : B → B → Set ℓP)
    (trans≤B : ∀ {x y z} → ≤B x y → ≤B y z → ≤B x z)
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW : CostedProofWitnessBy {ℓB = ℓB} {ℓP = ℓP} B ≤B Test W-pos)
  → BudgetedTruthPositivityBy {ℓT} {ℓW} {ℓB} {ℓP} B ≤B
fromCostedProofWitnessBy ≤B trans≤B {Test = Test} {W-pos = W-pos} PW =
  record
    { Test        = Test
    ; W-pos       = W-pos
    ; Observable≤ = λ b t → Σ (CostedProofWitnessBy.Proof PW t)
                           (λ p → ≤B (CostedProofWitnessBy.cost PW p) b)
    ; monoObs     = λ {b} {b′} {t} le (p , c≤) → p , trans≤B c≤ le
    ; positivity≤ = λ b t obs → CostedProofWitnessBy.check PW (proj₁ obs)
    }

-- Construct a budgeted truth positivity interface from a partial witness surface
-- plus a cost model on positivity witnesses.

fromCostedPartialWitness
  : ∀ {ℓT ℓW}
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW   : TP.PartialWitness Test W-pos)
    (cost : ∀ {t} → W-pos t → ℕ)
  → BudgetedTruthPositivity {ℓT} {ℓW} {ℓT ⊔ ℓW}
fromCostedPartialWitness {Test = Test} {W-pos = W-pos} PW cost =
  record
    { Test        = Test
    ; W-pos       = W-pos
    ; Observable≤ = λ b t → Σ (W-pos t)
                           (λ p → cost p ≤ℕ b × TP.PartialWitness.infer PW t ≡ inj₁ (t , p))
    ; monoObs     = λ {b} {b′} {t} le (p , c≤ , eq) → p , trans≤ℕ c≤ le , eq
    ; positivity≤ = λ b t obs → proj₁ obs
    }
