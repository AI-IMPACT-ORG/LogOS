{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.QNat where

open import LogOS.Prelude

open import LogOS.Prelude using (ℕ; zero; suc; _+_)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ; weakenRight)
open import LogOS.Prelude.NatExtra using (_⊔ℕ_; max-left; max-right; ⊔ℕ-least; +-assoc; +-zeroˡ; +-zeroʳ; ⊔ℕ-distrib-+ʳ; ⊔ℕ-distrib-+ˡ)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps; ScaleOpsLaws; BudgetOps)

-- Numeric prequantale+time adapter: costs are naturals with preorder ≤ and monoid +.
-- This is the default “step counting / time” adapter used by many demos.

private
  leAddLeft : ∀ b c → c ≤ℕ (b + c)
  leAddLeft zero    c = ≤ℕ-refl
  leAddLeft (suc b) c = weakenRight (leAddLeft b c)

  monoPlusRight : ∀ {a b c} → a ≤ℕ b → (a + c) ≤ℕ (b + c)
  monoPlusRight {b = b} {c = c} z≤n = leAddLeft b c
  monoPlusRight (s≤s p) = s≤s (monoPlusRight p)

  monoPlusLeft : ∀ {a b} → a ≤ℕ b → ∀ c → (c + a) ≤ℕ (c + b)
  monoPlusLeft p zero    = p
  monoPlusLeft p (suc c) = s≤s (monoPlusLeft p c)

  +-mono≤ℕ : ∀ {a a' b b'} → a ≤ℕ a' → b ≤ℕ b' → (a + b) ≤ℕ (a' + b')
  +-mono≤ℕ {a' = a'} a≤a' b≤b' =
    trans≤ℕ (monoPlusRight a≤a') (monoPlusLeft b≤b' a')

QNat : QAdapter lzero
QNat = record
  { Scale = ℕ
  ; _≤s_  = _≤ℕ_
  ; ≤s-refl = ≤ℕ-refl
  ; ≤s-trans = trans≤ℕ
  ; _⊔s_ = _⊔ℕ_
  ; ⊥s = zero
  ; ⊥s-least = λ _ → z≤n
  ; ⊔s-ub₁ = max-left
  ; ⊔s-ub₂ = max-right
  ; ⊔s-least = ⊔ℕ-least
  ; _·_   = _+_
  ; e     = zero
  ; ·-assoc = +-assoc
  ; ·-idl = +-zeroˡ
  ; ·-idr = +-zeroʳ
  ; ·-mono = +-mono≤ℕ
  ; ·-distl-⊔s = ⊔ℕ-distrib-+ʳ
  ; ·-distr-⊔s = ⊔ℕ-distrib-+ˡ
  ; _≤p_  = _≤ℕ_
  ; ≤p-refl = ≤ℕ-refl
  ; ≤p-trans = trans≤ℕ
  ; Time  = ℕ
  ; _+_   = _+_
  ; zero  = zero
  ; τ     = λ n → n
  ; +-assoc = +-assoc
  ; +-idl = +-zeroˡ
  ; +-idr = +-zeroʳ
  ; τ-+ = λ _ _ → refl
  ; τ-zero = refl
  }

scaleOps : ScaleOps QNat
scaleOps = record { budget = λ n → n ; steps = λ n → n }

scaleOpsLaws : ScaleOpsLaws QNat scaleOps
scaleOpsLaws = record { steps-budget-mono = λ le → le }

budgetOps : BudgetOps QNat
budgetOps = record { Ops = scaleOps ; laws = scaleOpsLaws }
