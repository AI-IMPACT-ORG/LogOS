{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.QNatMul where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.NatOrder using
  ( _≤ℕ_
  ; z≤n
  ; ≤ℕ-refl
  ; trans≤ℕ
  ; dec≤ℕ
  ; not≤→≥
  ; antisym≤ℕ
  )
open import Data.NatExtra using (_⊔ℕ_; max-left; max-right; ⊔ℕ-least; +-assoc; +-zeroˡ; +-zeroʳ)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps)

open import Data.NatLog2 using
  ( one
  ; plusR-zeroˡ
  ; plusR-sucˡ
  ; mul
  ; mul-assoc
  ; mul-monoL
  ; mul-monoR
  ; mul-mono₂
  ; exp₂
  ; exp₂-+
  ; log₂
  )

-- Max-choice lemmas (total order).

max-right-eq : ∀ {a b} → a ≤ℕ b → a ⊔ℕ b ≡ b
max-right-eq {a} {b} a≤b =
  antisym≤ℕ (⊔ℕ-least a≤b ≤ℕ-refl) (max-right a b)

max-left-eq : ∀ {a b} → b ≤ℕ a → a ⊔ℕ b ≡ a
max-left-eq {a} {b} b≤a =
  antisym≤ℕ (⊔ℕ-least ≤ℕ-refl b≤a) (max-left a b)

pow : ℕ → ℕ → ℕ
pow _ zero = one
pow a (suc n) = mul a (pow a n)

mul-idl : ∀ a → mul one a ≡ a
mul-idl zero = refl
mul-idl (suc a) =
  trans
    (plusR-sucˡ zero (mul one a))
    (cong suc (trans (plusR-zeroˡ (mul one a)) (mul-idl a)))

mul-idr : ∀ a → mul a one ≡ a
mul-idr _ = refl

-- Multiplication distributes over max by totality of ≤ℕ.
mul-distl-⊔ : ∀ a b c → mul (a ⊔ℕ b) c ≡ (mul a c) ⊔ℕ (mul b c)
mul-distl-⊔ a b c with dec≤ℕ a b
... | inj₁ a≤b rewrite max-right-eq a≤b | max-right-eq (mul-monoL a≤b c) = refl
... | inj₂ not≤ rewrite max-left-eq (not≤→≥ not≤) | max-left-eq (mul-monoL (not≤→≥ not≤) c) = refl

mul-distr-⊔ : ∀ a b c → mul a (b ⊔ℕ c) ≡ (mul a b) ⊔ℕ (mul a c)
mul-distr-⊔ a b c with dec≤ℕ b c
... | inj₁ b≤c rewrite max-right-eq b≤c | max-right-eq (mul-monoR a b≤c) = refl
... | inj₂ not≤ rewrite max-left-eq (not≤→≥ not≤) | max-left-eq (mul-monoR a (not≤→≥ not≤)) = refl

-- Adapter -------------------------------------------------------------------

QNatMul : QAdapter lzero
QNatMul = record
  { Scale = ℕ
  ; _≤s_ = _≤ℕ_
  ; ≤s-refl = ≤ℕ-refl
  ; ≤s-trans = trans≤ℕ
  ; _⊔s_ = _⊔ℕ_
  ; ⊥s = zero
  ; ⊥s-least = λ _ → z≤n
  ; ⊔s-ub₁ = max-left
  ; ⊔s-ub₂ = max-right
  ; ⊔s-least = ⊔ℕ-least
  ; _·_ = mul
  ; e = one
  ; ·-assoc = λ a b c → sym (mul-assoc a b c)
  ; ·-idl = mul-idl
  ; ·-idr = mul-idr
  ; ·-mono = mul-mono₂
  ; ·-distl-⊔s = mul-distl-⊔
  ; ·-distr-⊔s = mul-distr-⊔
  ; _≤p_ = _≤ℕ_
  ; ≤p-refl = ≤ℕ-refl
  ; ≤p-trans = trans≤ℕ
  ; Time = ℕ
  ; _+_ = _+_
  ; zero = zero
  ; τ = exp₂
  ; +-assoc = +-assoc
  ; +-idl = +-zeroˡ
  ; +-idr = +-zeroʳ
  ; τ-+ = exp₂-+
  ; τ-zero = refl
  }

-- Operational view: treat multiplicative scales as log₂ step budgets.
scaleOps : ScaleOps QNatMul
scaleOps = record { budget = log₂ ; steps = λ n → n }
