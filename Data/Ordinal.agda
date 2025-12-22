{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Ordinal where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (⊥; ¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.NatOrder public
  using (_≤ℕ_; z≤n; s≤s)
  renaming (≤ℕ-refl to ≤ℕ-reflᵢ; trans≤ℕ to ≤ℕ-transᵢ)

maxℕ : ℕ → ℕ → ℕ
maxℕ zero n = n
maxℕ (suc m) zero = suc m
maxℕ (suc m) (suc n) = suc (maxℕ m n)

-- Simple bounded ordinals: either a finite level (ℕ) or a designated limit ω.

data Ord : Set where
  fin : ℕ → Ord
  ω   : Ord

infix 4 _≤_ _≺_

_≤_ : Ord → Ord → Set
fin m ≤ fin n = m ≤ℕ n
fin m ≤ ω     = ⊤
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

≤ℕ-refl : ∀ n → n ≤ℕ n
≤ℕ-refl n = ≤ℕ-reflᵢ

≤ℕ-trans : ∀ {m n p} → m ≤ℕ n → n ≤ℕ p → m ≤ℕ p
≤ℕ-trans = ≤ℕ-transᵢ

≤ℕ-max-left : ∀ m n → m ≤ℕ maxℕ m n
≤ℕ-max-left zero n = z≤n
≤ℕ-max-left (suc m) zero = s≤s (≤ℕ-refl m)
≤ℕ-max-left (suc m) (suc n) = s≤s (≤ℕ-max-left m n)

≤ℕ-max-right : ∀ m n → n ≤ℕ maxℕ m n
≤ℕ-max-right zero n = ≤ℕ-refl n
≤ℕ-max-right (suc m) zero = z≤n
≤ℕ-max-right (suc m) (suc n) = s≤s (≤ℕ-max-right m n)

≤ℕ-suc : ∀ n → n ≤ℕ suc n
≤ℕ-suc zero = z≤n
≤ℕ-suc (suc n) = s≤s (≤ℕ-suc n)
