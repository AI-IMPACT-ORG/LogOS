{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.QNat2 where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; _+_)
open import Data.NatOrder using (_≤ℕ_; ≤ℕ-refl; trans≤ℕ)
open import Data.Product using (_×_; _,_; fst; snd)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps)

-- Two-axis numeric adapter:
-- - first component: “unitary/ordinary” work (depth/steps)
-- - second component: “nonunitary/measurement” events
--
-- This is small but high-leverage: it lets UniversalIR expose a genuinely
-- physical resource split without changing the semantic center (`observe`).

infix 4 _≤₂_
_≤₂_ : (ℕ × ℕ) → (ℕ × ℕ) → Set
(a₁ , b₁) ≤₂ (a₂ , b₂) = (a₁ ≤ℕ a₂) × (b₁ ≤ℕ b₂)

infixl 7 _+₂_
_+₂_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
(a₁ , b₁) +₂ (a₂ , b₂) = (a₁ + a₂ , b₁ + b₂)

zero₂ : (ℕ × ℕ)
zero₂ = (zero , zero)

QNat2 : QAdapter lzero
QNat2 = record
  { Scale = ℕ × ℕ
  ; _≤s_  = _≤₂_
  ; _·_   = _+₂_
  ; e     = zero₂
  ; _≤p_  = _≤₂_
  ; Time  = ℕ
  ; _+_   = _+_
  ; zero  = zero
  ; τ     = λ n → (n , zero)
  }

scaleOps : ScaleOps QNat2
scaleOps = record { budget = λ g → fst g ; steps = λ n → n }

-- Coherence: interpreting the canonical embedding `τ` as a step budget yields
-- exactly the original step count.
steps-budget-τ
  : ∀ n
  → ScaleOps.steps scaleOps (ScaleOps.budget scaleOps (QAdapter.τ QNat2 n)) ≡ n
steps-budget-τ _ = refl
