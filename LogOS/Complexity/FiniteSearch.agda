{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.FiniteSearch where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥)

open import LogOS.Prelude using (ℕ; zero; suc)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude using (Σ; _,_)

-- Finite indices at arbitrary universe level (so bounded search lives in `Set ℓ`).

data Finℓ {ℓ : Level} : ℕ → Set ℓ where
  fzero : ∀ {n} → Finℓ {ℓ} (suc n)
  fsuc  : ∀ {n} → Finℓ {ℓ} n → Finℓ {ℓ} (suc n)

toNat : ∀ {ℓ} {n} → Finℓ {ℓ} n → ℕ
toNat {n = suc _} fzero = zero
toNat (fsuc i) = suc (toNat i)

module Search where
  ExistsFin : ∀ {ℓ} {n : ℕ} → (Pred : Finℓ {ℓ} n → Set ℓ) → Set ℓ
  ExistsFin Pred = Σ _ (λ i → Pred i)

  searchFin
    : ∀ {ℓ} (n : ℕ) (Pred : Finℓ {ℓ} n → Set ℓ)
      (dec : ∀ i → Pred i ⊎ ¬ Pred i)
    → ExistsFin Pred ⊎ ¬ ExistsFin Pred
  searchFin zero Pred dec = inj₂ (λ { (i , _) → case i })
    where
      case : ∀ {ℓ} → Finℓ {ℓ} zero → ⊥ {lzero}
      case ()
  searchFin (suc n) Pred dec with dec fzero
  ... | inj₁ p = inj₁ (fzero , p)
  ... | inj₂ np with searchFin n (λ i → Pred (fsuc i)) (λ i → dec (fsuc i))
  ...   | inj₁ (i , pi) = inj₁ (fsuc i , pi)
  ...   | inj₂ none = inj₂ (λ { (fzero , p) → np p ; (fsuc i , p) → none (i , p) })

