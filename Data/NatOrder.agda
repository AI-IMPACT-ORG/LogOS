{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.NatOrder where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)
open import LogOS.Syntax.Prop using (¬_; ⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

infix 4 _≤ℕ_

data _≤ℕ_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ℕ n
  s≤s : ∀ {m n} → m ≤ℕ n → suc m ≤ℕ suc n

≤ℕ-refl : ∀ {n} → n ≤ℕ n
≤ℕ-refl {n = zero} = z≤n
≤ℕ-refl {n = suc n} = s≤s ≤ℕ-refl

trans≤ℕ : ∀ {a b c : ℕ} → a ≤ℕ b → b ≤ℕ c → a ≤ℕ c
trans≤ℕ z≤n _ = z≤n
trans≤ℕ (s≤s ab) (s≤s bc) = s≤s (trans≤ℕ ab bc)

weakenRight : ∀ {a b : ℕ} → a ≤ℕ b → a ≤ℕ suc b
weakenRight z≤n = z≤n
weakenRight (s≤s ab) = s≤s (weakenRight ab)

dec≤ℕ : ∀ m n → m ≤ℕ n ⊎ ¬ (m ≤ℕ n)
dec≤ℕ zero    n       = inj₁ z≤n
dec≤ℕ (suc m) zero    = inj₂ (λ ())
dec≤ℕ (suc m) (suc n) with dec≤ℕ m n
... | inj₁ mn = inj₁ (s≤s mn)
... | inj₂ nmn = inj₂ (λ { (s≤s mn) → nmn mn })

-- Naturals are total: for any m,n either m ≤ n or n ≤ m.
total≤ℕ : ∀ m n → m ≤ℕ n ⊎ n ≤ℕ m
total≤ℕ zero n = inj₁ z≤n
total≤ℕ (suc m) zero = inj₂ z≤n
total≤ℕ (suc m) (suc n) with total≤ℕ m n
... | inj₁ mn = inj₁ (s≤s mn)
... | inj₂ nm = inj₂ (s≤s nm)

⊥-elim : ∀ {ℓ} {A : Set ℓ} → ⊥ {ℓ} → A
⊥-elim ()

not≤→≥ : ∀ {m n} → ¬ (m ≤ℕ n) → n ≤ℕ m
not≤→≥ {m} {n} not with total≤ℕ n m
... | inj₁ nm = nm
... | inj₂ mn = ⊥-elim (not mn)
