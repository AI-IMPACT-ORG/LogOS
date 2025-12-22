{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Std where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core
open import Data.Bool using (Bool; true; false)

-- Tiny “standard library” lemmas used throughout UniversalIR.

-- Naturals ------------------------------------------------------------------

+-zeroʳ : ∀ n → n + 0 ≡ n
+-zeroʳ zero    = refl
+-zeroʳ (suc n) = cong suc (+-zeroʳ n)

+-sucʳ : ∀ m n → m + suc n ≡ suc (m + n)
+-sucʳ zero    _ = refl
+-sucʳ (suc m) n = cong suc (+-sucʳ m n)

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero    _ _ = refl
+-assoc (suc x) y z = cong suc (+-assoc x y z)

swapSuc : ∀ m n → (suc m) + n ≡ m + suc n
swapSuc m n = trans refl (sym (+-sucʳ m n))

-- Decidable equality witness for `_==ℕ_` (from `LogOS.Domain.UniversalIR.Core`).

==ℕ-true→≡ : ∀ m n → (m ==ℕ n) ≡ true → m ≡ n
==ℕ-true→≡ zero    zero    _   = refl
==ℕ-true→≡ zero    (suc _) ()
==ℕ-true→≡ (suc _) zero    ()
==ℕ-true→≡ (suc m) (suc n) eq = cong suc (==ℕ-true→≡ m n eq)

-- Subtraction (`_∸_` from `LogOS.Domain.UniversalIR.Core`) -------------------

∸-zeroʳ : ∀ n → n ∸ 0 ≡ n
∸-zeroʳ zero    = refl
∸-zeroʳ (suc _) = refl

∸-one-suc : ∀ n → (suc n) ∸ (suc zero) ≡ n
∸-one-suc n rewrite ∸-zeroʳ n = refl

-- Multiplication ------------------------------------------------------------

*-oneʳ : ∀ n → n * (suc zero) ≡ n
*-oneʳ zero    = refl
*-oneʳ (suc n) = cong suc (*-oneʳ n)

*-oneˡ : ∀ n → (suc zero) * n ≡ n
*-oneˡ n = trans refl (+-zeroʳ n)

*-distribˡ-+ : ∀ x y z → (x + y) * z ≡ (x * z) + (y * z)
*-distribˡ-+ zero    y z = refl
*-distribˡ-+ (suc x) y z =
  trans
    (cong (λ t → z + t) (*-distribˡ-+ x y z))
    (sym (+-assoc z (x * z) (y * z)))

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc zero    _ _ = refl
*-assoc (suc a) b c =
  trans
    (*-distribˡ-+ b (a * b) c)
    (cong (λ t → (b * c) + t) (*-assoc a b c))

-- Church numerals -----------------------------------------------------------

countChurchBody-iterApp : ∀ n → countChurchBody (iterApp n (var 1) (var 0)) ≡ n
countChurchBody-iterApp zero    = refl
countChurchBody-iterApp (suc n) = cong suc (countChurchBody-iterApp n)

decodeChurch-church : ∀ n → decodeChurch (church n) ≡ n
decodeChurch-church n = countChurchBody-iterApp n

-- Simulation ----------------------------------------------------------------

simulate-+ : ∀ n m u → simulate (n + m) u ≡ simulate m (simulate n u)
simulate-+ zero    m u = refl
simulate-+ (suc n) m u = simulate-+ n m (stepU u)
