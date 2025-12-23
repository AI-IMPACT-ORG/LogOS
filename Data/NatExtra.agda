{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.NatExtra where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import LogOS.Prelude
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.NatOrder as NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; trans≤ℕ; weakenRight)

infixl 6 _⊔ℕ_

_⊔ℕ_ : ℕ → ℕ → ℕ
zero ⊔ℕ n = n
suc m ⊔ℕ zero = suc m
suc m ⊔ℕ suc n = suc (m ⊔ℕ n)

⊔ℕ-zeroʳ : ∀ n → n ⊔ℕ zero ≡ n
⊔ℕ-zeroʳ zero = refl
⊔ℕ-zeroʳ (suc _) = refl

⊔ℕ-zeroˡ : ∀ n → zero ⊔ℕ n ≡ n
⊔ℕ-zeroˡ _ = refl

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

-- Addition ------------------------------------------------------------------

+-zeroˡ : ∀ n → zero + n ≡ n
+-zeroˡ zero = refl
+-zeroˡ (suc _) = refl

+-zeroʳ : ∀ n → n + zero ≡ n
+-zeroʳ zero = refl
+-zeroʳ (suc n) = cong suc (+-zeroʳ n)

+-sucʳ : ∀ m n → m + suc n ≡ suc (m + n)
+-sucʳ zero _ = refl
+-sucʳ (suc m) n = cong suc (+-sucʳ m n)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero _ _ = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

-- Max/⊔ as least upper bound ------------------------------------------------

⊔ℕ-least : ∀ {a b c} → a ≤ℕ c → b ≤ℕ c → (a ⊔ℕ b) ≤ℕ c
⊔ℕ-least {a = zero} {b = b} {_} _ b≤ = b≤
⊔ℕ-least {a = suc a} {b = zero} {_} a≤ _ = a≤
⊔ℕ-least {a = suc _} {b = suc _} {c = zero} () _
⊔ℕ-least {a = suc a} {b = suc b} {c = suc c} (s≤s a≤) (s≤s b≤) =
  s≤s (⊔ℕ-least a≤ b≤)

-- Distributivity: (+) preserves max (finite joins) --------------------------

⊔ℕ-distrib-+ʳ : ∀ a b c → (a ⊔ℕ b) + c ≡ (a + c) ⊔ℕ (b + c)
⊔ℕ-distrib-+ʳ a b zero
  rewrite +-zeroʳ (a ⊔ℕ b)
        | +-zeroʳ a
        | +-zeroʳ b
        = refl
⊔ℕ-distrib-+ʳ a b (suc c)
  rewrite +-sucʳ (a ⊔ℕ b) c
        | +-sucʳ a c
        | +-sucʳ b c
        = cong suc (⊔ℕ-distrib-+ʳ a b c)

⊔ℕ-distrib-+ˡ : ∀ a b c → a + (b ⊔ℕ c) ≡ (a + b) ⊔ℕ (a + c)
⊔ℕ-distrib-+ˡ zero b c = refl
⊔ℕ-distrib-+ˡ (suc a) b c = cong suc (⊔ℕ-distrib-+ˡ a b c)
