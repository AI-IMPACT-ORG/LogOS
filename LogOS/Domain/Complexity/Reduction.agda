{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Reduction where

-- Standard many-one reductions, with optional polynomial size bounds.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro; ↔-sym)

open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_)
open import Data.Product using (Σ; _,_; _×_)

open import LogOS.Domain.Complexity.Poly using (PolyPred)
open import LogOS.Domain.Complexity.LanguageWitness using (DeciderI; reindexDeciderI)
open import LogOS.Computation.Decider using (mapDecider)

record ManyOneReduction
  {ℓI₁ ℓI₂ ℓP ℓQ : Level}
  (Input₁ : Set ℓI₁)
  (Input₂ : Set ℓI₂)
  (P : Input₁ → Set ℓP)
  (Q : Input₂ → Set ℓQ)
  : Set (lsuc (ℓI₁ ⊔ ℓI₂ ⊔ ℓP ⊔ ℓQ)) where
  field
    map   : Input₁ → Input₂
    sound : ∀ x → P x → Q (map x)
    complete : ∀ x → Q (map x) → P x

  correctness : ∀ x → P x ↔ Q (map x)
  correctness x = intro (sound x) (complete x)

-- Decider transport along a reduction.
deciderFromReduction
  : ∀ {ℓI₁ ℓI₂ ℓPQ}
    {Input₁ : Set ℓI₁} {Input₂ : Set ℓI₂}
    {P : Input₁ → Set ℓPQ} {Q : Input₂ → Set ℓPQ}
  → ManyOneReduction Input₁ Input₂ P Q
  → DeciderI Input₂ Q
  → DeciderI Input₁ P
deciderFromReduction R D =
  mapDecider (λ x → ↔-sym (ManyOneReduction.correctness R x))
    (reindexDeciderI (ManyOneReduction.map R) _ D)

record PolyReduction
  {ℓI₁ ℓI₂ ℓP ℓQ : Level}
  (Input₁ : Set ℓI₁)
  (Input₂ : Set ℓI₂)
  (P : Input₁ → Set ℓP)
  (Q : Input₂ → Set ℓQ)
  (size₁ : Input₁ → ℕ)
  (size₂ : Input₂ → ℕ)
  (poly : PolyPred)
  : Set (lsuc (ℓI₁ ⊔ ℓI₂ ⊔ ℓP ⊔ ℓQ)) where
  open PolyPred poly
  field
    red : ManyOneReduction Input₁ Input₂ P Q
    bound : ∀ x → Σ (ℕ → ℕ) (λ f → isPoly f × size₂ (ManyOneReduction.map red x) ≤ℕ f (size₁ x))
