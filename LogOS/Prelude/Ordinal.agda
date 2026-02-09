{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.Ordinal where

open import LogOS.Prelude
open import LogOS.Prelude.Empty using (⊥)

open import LogOS.Prelude.NatOrder public
  using (_≤ℕ_; z≤n; s≤s; ¬suc≤self)
  renaming (≤ℕ-refl to ≤ℕ-reflᶦ; trans≤ℕ to ≤ℕ-transᶦ)

open import LogOS.Prelude.NatExtra as NatExtra using (_⊔ℕ_; max-left; max-right; ≤ℕ-suc)

maxℕ : ℕ → ℕ → ℕ
maxℕ = _⊔ℕ_

-- Simple bounded ordinals: either a finite level (ℕ) or a designated top ω.
-- Note: ω is a cap, so `succ ω = ω` (bounded successor).

data Ord : Set where
  fin : ℕ → Ord
  ω   : Ord

infix 4 _≤_ _≺_

_≤_ : Ord → Ord → Set
fin m ≤ fin n = m ≤ℕ n
fin _ ≤ ω     = ⊤
ω ≤ fin _     = ⊥
ω ≤ ω         = ⊤

_≺_ : Ord → Ord → Set
α ≺ β = α ≤ β × ¬ (β ≤ α)

succ : Ord → Ord
succ (fin n) = fin (suc n)
succ ω = ω

join : Ord → Ord → Ord
join (fin m) (fin n) = fin (maxℕ m n)
join ω _ = ω
join (fin _) ω = ω

isLimit : Ord → Set
isLimit (fin zero) = ⊥
isLimit (fin (suc _)) = ⊥
isLimit ω = ⊤

-- Bounded successor facts.

succ-ω-fixed : succ ω ≡ ω
succ-ω-fixed = refl

succ-fin-strict : ∀ n → fin n ≺ succ (fin n)
succ-fin-strict n = ≤ℕ-suc n , ¬suc≤self

≤ℕ-refl : ∀ n → n ≤ℕ n
≤ℕ-refl _ = ≤ℕ-reflᶦ

≤ℕ-trans : ∀ {m n p} → m ≤ℕ n → n ≤ℕ p → m ≤ℕ p
≤ℕ-trans = ≤ℕ-transᶦ

≤ℕ-max-left : ∀ m n → m ≤ℕ maxℕ m n
≤ℕ-max-left = max-left

≤ℕ-max-right : ∀ m n → n ≤ℕ maxℕ m n
≤ℕ-max-right = max-right
