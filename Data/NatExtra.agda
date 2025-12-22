{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.NatExtra where

open import Data.Nat using (ℕ; zero; suc)
open import LogOS.Prelude
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.NatOrder as NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ; weakenRight)

infixl 6 _⊔ℕ_

_⊔ℕ_ : ℕ → ℕ → ℕ
zero ⊔ℕ n = n
suc m ⊔ℕ zero = suc m
suc m ⊔ℕ suc n = suc (m ⊔ℕ n)

⊔-comm : ∀ m n → m ⊔ℕ n ≡ n ⊔ℕ m
⊔-comm zero zero = refl
⊔-comm zero (suc n) = refl
⊔-comm (suc m) zero = refl
⊔-comm (suc m) (suc n) = cong suc (⊔-comm m n)

max-left : ∀ m n → m ≤ℕ (m ⊔ℕ n)
max-left zero n = z≤n
max-left (suc m) zero = s≤s ≤ℕ-refl
max-left (suc m) (suc n) = s≤s (max-left m n)

max-right : ∀ m n → n ≤ℕ (m ⊔ℕ n)
max-right m n rewrite ⊔-comm m n = max-left n m

≤ℕ-suc : ∀ n → n ≤ℕ suc n
≤ℕ-suc n = weakenRight ≤ℕ-refl
