{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.QNat2 where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ; weakenRight)
open import Data.NatExtra using (_⊔ℕ_; max-left; max-right; ⊔ℕ-least; +-assoc; +-zeroˡ; +-zeroʳ; ⊔ℕ-distrib-+ʳ; ⊔ℕ-distrib-+ˡ)
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

infixl 6 _⊔₂_
_⊔₂_ : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
(a₁ , b₁) ⊔₂ (a₂ , b₂) = (a₁ ⊔ℕ a₂ , b₁ ⊔ℕ b₂)

zero₂ : (ℕ × ℕ)
zero₂ = (zero , zero)

QNat2 : QAdapter lzero
QNat2 = record
  { Scale = ℕ × ℕ
  ; _≤s_  = _≤₂_
  ; ≤s-refl = (≤ℕ-refl , ≤ℕ-refl)
  ; ≤s-trans = λ { {a₁ , b₁} {a₂ , b₂} {a₃ , b₃} (a12 , b12) (a23 , b23) →
      trans≤ℕ a12 a23 , trans≤ℕ b12 b23
    }
  ; _⊔s_ = _⊔₂_
  ; ⊥s = zero₂
  ; ⊥s-least = λ { (a , b) → z≤n , z≤n }
  ; ⊔s-ub₁ = λ { (a₁ , b₁) (a₂ , b₂) → max-left a₁ a₂ , max-left b₁ b₂ }
  ; ⊔s-ub₂ = λ { (a₁ , b₁) (a₂ , b₂) → max-right a₁ a₂ , max-right b₁ b₂ }
  ; ⊔s-least = λ { {a₁ , b₁} {a₂ , b₂} {a₃ , b₃} (a13 , b13) (a23 , b23) →
      ⊔ℕ-least a13 a23 , ⊔ℕ-least b13 b23
    }
  ; _·_   = _+₂_
  ; e     = zero₂
  ; ·-assoc = λ { (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) →
      cong₂ _,_ (+-assoc a₁ a₂ a₃) (+-assoc b₁ b₂ b₃)
    }
  ; ·-idl = λ { (a , b) → cong₂ _,_ (+-zeroˡ a) (+-zeroˡ b) }
  ; ·-idr = λ { (a , b) → cong₂ _,_ (+-zeroʳ a) (+-zeroʳ b) }
  ; ·-mono = ·-mono₂
  ; ·-distl-⊔s = λ { (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) →
      cong₂ _,_ (⊔ℕ-distrib-+ʳ a₁ a₂ a₃) (⊔ℕ-distrib-+ʳ b₁ b₂ b₃)
    }
  ; ·-distr-⊔s = λ { (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) →
      cong₂ _,_ (⊔ℕ-distrib-+ˡ a₁ a₂ a₃) (⊔ℕ-distrib-+ˡ b₁ b₂ b₃)
    }
  ; _≤p_  = _≤₂_
  ; ≤p-refl = (≤ℕ-refl , ≤ℕ-refl)
  ; ≤p-trans = λ { {a₁ , b₁} {a₂ , b₂} {a₃ , b₃} (a12 , b12) (a23 , b23) →
      trans≤ℕ a12 a23 , trans≤ℕ b12 b23
    }
  ; Time  = ℕ
  ; _+_   = _+_
  ; zero  = zero
  ; τ     = λ n → (n , zero)
  ; +-assoc = +-assoc
  ; +-idl = +-zeroˡ
  ; +-idr = +-zeroʳ
  ; τ-+ = λ _ _ → refl
  ; τ-zero = refl
  }
  where
    leAddLeft : ∀ b c → c ≤ℕ (b + c)
    leAddLeft zero    c = ≤ℕ-refl
    leAddLeft (suc b) c = weakenRight (leAddLeft b c)

    monoPlusRight : ∀ {a b c} → a ≤ℕ b → (a + c) ≤ℕ (b + c)
    monoPlusRight {b = b} {c = c} z≤n = leAddLeft b c
    monoPlusRight (s≤s p) = s≤s (monoPlusRight p)

    monoPlusLeft : ∀ {a b} → a ≤ℕ b → ∀ c → (c + a) ≤ℕ (c + b)
    monoPlusLeft p zero    = p
    monoPlusLeft p (suc c) = s≤s (monoPlusLeft p c)

    +-mono : ∀ {a a' b b'} → a ≤ℕ a' → b ≤ℕ b' → (a + b) ≤ℕ (a' + b')
    +-mono {a' = a'} a≤a' b≤b' =
      trans≤ℕ (monoPlusRight a≤a') (monoPlusLeft b≤b' a')

    ·-mono₂
      : ∀ {a b c d}
      → a ≤₂ b
      → c ≤₂ d
      → (a +₂ c) ≤₂ (b +₂ d)
    ·-mono₂ {a = a₁ , a₂} {b = b₁ , b₂} {c = c₁ , c₂} {d = d₁ , d₂}
      (a1≤b1 , a2≤b2) (c1≤d1 , c2≤d2) =
        +-mono a1≤b1 c1≤d1 , +-mono a2≤b2 c2≤d2

-- Canonical embedding for the “measurement axis” (second component).
--
-- This mirrors `τ` (which targets the work/step axis). It is not part of the
-- minimal `QAdapter` record because the core only needs *one* time embedding,
-- but it is convenient for universality/physics-facing examples.

μ : ℕ → QAdapter.Scale QNat2
μ n = (zero , n)

μ-+ : ∀ n m → μ (n + m) ≡ (QAdapter._·_ QNat2 (μ n) (μ m))
μ-+ _ _ = refl

μ-zero : μ zero ≡ QAdapter.e QNat2
μ-zero = refl

-- Monotonicity of the canonical embeddings (w.r.t. ≤ℕ).
--
-- These are often the only order facts needed to build honest cost envelopes
-- in downstream developments.

τ-mono : ∀ {n m} → n ≤ℕ m → QAdapter._≤s_ QNat2 (QAdapter.τ QNat2 n) (QAdapter.τ QNat2 m)
τ-mono nm = nm , ≤ℕ-refl

μ-mono : ∀ {n m} → n ≤ℕ m → QAdapter._≤s_ QNat2 (μ n) (μ m)
μ-mono nm = ≤ℕ-refl , nm

scaleOps : ScaleOps QNat2
scaleOps = record { budget = λ g → fst g ; steps = λ n → n }

-- Coherence: interpreting the canonical embedding `τ` as a step budget yields
-- exactly the original step count.
steps-budget-τ
  : ∀ n
  → ScaleOps.steps scaleOps (ScaleOps.budget scaleOps (QAdapter.τ QNat2 n)) ≡ n
steps-budget-τ _ = refl
