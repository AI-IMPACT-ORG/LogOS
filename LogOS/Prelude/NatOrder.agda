{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.NatOrder where

open import LogOS.Prelude
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude.Empty using (⊥-elim)

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
dec≤ℕ zero    _       = inj₁ z≤n
dec≤ℕ (suc _) zero    = inj₂ (λ ())
dec≤ℕ (suc m) (suc n) with dec≤ℕ m n
... | inj₁ mn  = inj₁ (s≤s mn)
... | inj₂ nmn = inj₂ (λ { (s≤s mn) → nmn mn })

-- Naturals are total: for any m,n either m ≤ n or n ≤ m.
total≤ℕ : ∀ m n → m ≤ℕ n ⊎ n ≤ℕ m
total≤ℕ zero    _       = inj₁ z≤n
total≤ℕ (suc _) zero    = inj₂ z≤n
total≤ℕ (suc m) (suc n) with total≤ℕ m n
... | inj₁ mn = inj₁ (s≤s mn)
... | inj₂ nm = inj₂ (s≤s nm)

not≤→≥ : ∀ {m n} → ¬ (m ≤ℕ n) → n ≤ℕ m
not≤→≥ {m} {n} not with total≤ℕ n m
... | inj₁ nm = nm
... | inj₂ mn = ⊥-elim (not mn)

antisym≤ℕ : ∀ {a b} → a ≤ℕ b → b ≤ℕ a → a ≡ b
antisym≤ℕ z≤n z≤n = refl
antisym≤ℕ (s≤s ab) (s≤s ba) = cong suc (antisym≤ℕ ab ba)

-- No natural is ≥ its successor.
¬suc≤self : ∀ {n} → ¬ (suc n ≤ℕ n)
¬suc≤self {zero} ()
¬suc≤self {suc n} (s≤s sn≤n) = ¬suc≤self sn≤n

split≤suc : ∀ {k d} → k ≤ℕ suc d → (k ≤ℕ d) ⊎ (k ≡ suc d)
split≤suc {k = zero} {_} _ = inj₁ z≤n
split≤suc {k = suc k} {d = zero} (s≤s k≤0) =
  inj₂ (cong suc (antisym≤ℕ k≤0 z≤n))
split≤suc {k = suc k} {d = suc d} (s≤s k≤sd) with split≤suc {k = k} {d = d} k≤sd
... | inj₁ k≤d = inj₁ (s≤s k≤d)
... | inj₂ k≡  = inj₂ (cong suc k≡)
