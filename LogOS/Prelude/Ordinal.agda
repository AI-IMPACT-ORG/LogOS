{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.Ordinal where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ¬_)

open import LogOS.Prelude.NatOrder public
  using (_≤ℕ_; z≤n; s≤s; ¬suc≤self)
  renaming (≤ℕ-refl to ≤ℕ-reflᶦ; trans≤ℕ to ≤ℕ-transᶦ)

maxℕ : ℕ → ℕ → ℕ
maxℕ zero n = n
maxℕ (suc m) zero = suc m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

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

≤ℕ-suc : ∀ n → n ≤ℕ suc n
≤ℕ-suc zero = z≤n
≤ℕ-suc (suc n) = s≤s (≤ℕ-suc n)

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
≤ℕ-max-left zero _ = z≤n
≤ℕ-max-left (suc m) zero = s≤s (≤ℕ-refl m)
≤ℕ-max-left (suc m) (suc n) = s≤s (≤ℕ-max-left m n)

≤ℕ-max-right : ∀ m n → n ≤ℕ maxℕ m n
≤ℕ-max-right zero n = ≤ℕ-refl n
≤ℕ-max-right (suc _) zero = z≤n
≤ℕ-max-right (suc m) (suc n) = s≤s (≤ℕ-max-right m n)
