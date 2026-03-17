{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.NatQAdapter where

-- Concrete quantitative adapter on natural numbers.
--
-- Reading:
-- - scale = natural-number budget/grade
-- - refinement = ordinary `≤`
-- - join = `max`
-- - sequential composition = addition

open import LogOS.Prelude
open import LogOS.Prelude.Nat.Order using
  (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl; ≤ℕ-trans)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter; QClock)

max : ℕ → ℕ → ℕ
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-idr : ∀ a → a + zero ≡ a
+-idr zero = refl
+-idr (suc a) = cong suc (+-idr a)

≤ℕ-suc-right : ∀ {m n} → m ≤ℕ n → m ≤ℕ suc n
≤ℕ-suc-right z≤n = z≤n
≤ℕ-suc-right (s≤s p) = s≤s (≤ℕ-suc-right p)

right≤+ : ∀ a b → b ≤ℕ a + b
right≤+ zero b = ≤ℕ-refl
right≤+ (suc a) b = ≤ℕ-suc-right (right≤+ a b)

≤ℕ-+-mono : ∀ {a b c d} → a ≤ℕ b → c ≤ℕ d → a + c ≤ℕ b + d
≤ℕ-+-mono z≤n c≤d = ≤ℕ-trans c≤d (right≤+ _ _)
≤ℕ-+-mono (s≤s a≤b) c≤d = s≤s (≤ℕ-+-mono a≤b c≤d)

≤ℕ-maxL : ∀ a b → a ≤ℕ max a b
≤ℕ-maxL zero b = z≤n
≤ℕ-maxL (suc a) zero = ≤ℕ-refl
≤ℕ-maxL (suc a) (suc b) = s≤s (≤ℕ-maxL a b)

≤ℕ-maxR : ∀ a b → b ≤ℕ max a b
≤ℕ-maxR zero b = ≤ℕ-refl
≤ℕ-maxR (suc a) zero = z≤n
≤ℕ-maxR (suc a) (suc b) = s≤s (≤ℕ-maxR a b)

≤ℕ-maxLeast : ∀ {a b c} → a ≤ℕ c → b ≤ℕ c → max a b ≤ℕ c
≤ℕ-maxLeast {zero} {b} a≤c b≤c = b≤c
≤ℕ-maxLeast {suc a} {zero} a≤c b≤c = a≤c
≤ℕ-maxLeast {suc a} {suc b} (s≤s a≤c) (s≤s b≤c) =
  s≤s (≤ℕ-maxLeast a≤c b≤c)

max-absorbs-right : ∀ {a b} → a ≤ℕ b → max a b ≡ b
max-absorbs-right {zero} a≤b = refl
max-absorbs-right {suc a} {suc b} (s≤s a≤b) =
  cong suc (max-absorbs-right a≤b)

max-absorbs-left : ∀ {a b} → b ≤ℕ a → max a b ≡ a
max-absorbs-left {zero} {zero} z≤n = refl
max-absorbs-left {suc a} {zero} z≤n = refl
max-absorbs-left {suc a} {suc b} (s≤s b≤a) =
  cong suc (max-absorbs-left b≤a)

+-distl-max : ∀ a b c → max a b + c ≡ max (a + c) (b + c)
+-distl-max zero b c =
  sym (max-absorbs-right (right≤+ b c))
+-distl-max (suc a) zero c =
  sym (max-absorbs-left (≤ℕ-suc-right (right≤+ a c)))
+-distl-max (suc a) (suc b) c = cong suc (+-distl-max a b c)

+-distr-max : ∀ a b c → a + max b c ≡ max (a + b) (a + c)
+-distr-max zero b c = refl
+-distr-max (suc a) b c = cong suc (+-distr-max a b c)

natQAdapter : QAdapter lzero
natQAdapter =
  record
    { core =
        record
          { Scale = ℕ
          ; _≤s_ = _≤ℕ_
          ; ≤s-refl = ≤ℕ-refl
          ; ≤s-trans = ≤ℕ-trans
          ; _⊔s_ = max
          ; ⊥s = zero
          ; ⊥s-least = λ _ → z≤n
          ; ⊔s-ub₁ = ≤ℕ-maxL
          ; ⊔s-ub₂ = ≤ℕ-maxR
          ; ⊔s-least = ≤ℕ-maxLeast
          ; _·_ = _+_
          ; e = zero
          ; ·-mono = ≤ℕ-+-mono
          ; _≤p_ = _≤ℕ_
          ; ≤p-refl = ≤ℕ-refl
          ; ≤p-trans = ≤ℕ-trans
          }
    ; ·-assoc = +-assoc
    ; ·-idl = λ _ → refl
    ; ·-idr = +-idr
    ; ·-distl-⊔s = +-distl-max
    ; ·-distr-⊔s = +-distr-max
    }

natQClock : QClock natQAdapter
natQClock =
  record
    { Time = ℕ
    ; _+_ = _+_
    ; zero = zero
    ; τ = λ t → t
    ; +-assoc = +-assoc
    ; +-idl = λ _ → refl
    ; +-idr = +-idr
    ; τ-+ = λ _ _ → refl
    ; τ-zero = refl
    }
