{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.RegulatedPartition where

open import LogOS.Prelude
  hiding (_+_; _*_)

open import Data.Fin using (Fin; fzero; fsuc; toℕ)

open import LogOS.Algebra.Ring

-- Minimal algebraic laws needed to factor finite nested sums into products.
-- This is intentionally small: the regulator identity needs only left unit for `*`
-- and right distributivity.

record SemiringLaws {ℓ : Level} (R : Ring {ℓ}) : Set (lsuc ℓ) where
  field
    *-idL    : ∀ x → Ring._*_ R (Ring.1# R) x ≡ x
    distribR : ∀ a b c →
      Ring._*_ R (Ring._+_ R a b) c
      ≡
      Ring._+_ R (Ring._*_ R a c) (Ring._*_ R b c)

open SemiringLaws public

-- Standard power in a ring-like carrier (no laws assumed beyond definitional recursion).

powR : ∀ {ℓ} (R : Ring {ℓ}) → Ring.Carrier R → ℕ → Ring.Carrier R
powR R x zero    = Ring.1# R
powR R x (suc n) = Ring._*_ R x (powR R x n)

-- Geometric partial sum: Σ_{k=0..n} x^k.

sumPow : ∀ {ℓ} (R : Ring {ℓ}) → Ring.Carrier R → ℕ → Ring.Carrier R
sumPow R x zero    = Ring.1# R
sumPow R x (suc n) = Ring._+_ R (sumPow R x n) (powR R x (suc n))

-- Multiply a geometric partial sum into a right factor without assuming distributivity
-- up front: Σ_{k=0..n} x^k * y, computed by recursion.

sumPowMul
  : ∀ {ℓ} (R : Ring {ℓ})
  → Ring.Carrier R → ℕ → Ring.Carrier R → Ring.Carrier R
sumPowMul R x zero    y = y
sumPowMul R x (suc n) y =
  Ring._+_ R (sumPowMul R x n y) (Ring._*_ R (powR R x (suc n)) y)

sumPowMul≡sumPow*_
  : ∀ {ℓ} {R : Ring {ℓ}}
    (L : SemiringLaws R)
    (x : Ring.Carrier R)
    (n : ℕ)
    (y : Ring.Carrier R)
  → sumPowMul R x n y ≡ Ring._*_ R (sumPow R x n) y
sumPowMul≡sumPow*_ {R = R} L x zero y =
  sym (SemiringLaws.*-idL L y)
sumPowMul≡sumPow*_ {R = R} L x (suc n) y =
  trans
    (cong (λ t → Ring._+_ R t (Ring._*_ R (powR R x (suc n)) y))
          (sumPowMul≡sumPow*_ {R = R} L x n y))
    (sym (SemiringLaws.distribR L (sumPow R x n) (powR R x (suc n)) y))

infix 0 sumPowMul≡sumPow*_

-- A finite regulator: n modes, each with a cutoff on the exponent.

record Regulator {ℓM : Level} (Mode : Set ℓM) : Set (lsuc ℓM) where
  field
    n      : ℕ
    mode   : Fin n → Mode
    cutoff : Fin n → ℕ

open Regulator public

-- Finite partition function (sum-form): nested finite sums over exponent vectors.

Z-sum
  : ∀ {ℓ ℓM}
    (R : Ring {ℓ})
    (L : SemiringLaws R)
    {Mode : Set ℓM}
  → (n : ℕ)
  → (mode   : Fin n → Mode)
  → (cutoff : Fin n → ℕ)
  → (weight : Mode → Ring.Carrier R)
  → Ring.Carrier R
Z-sum R L zero    mode cutoff weight = Ring.1# R
Z-sum R L (suc n) mode cutoff weight =
  sumPowMul R
    (weight (mode fzero))
    (cutoff fzero)
    (Z-sum R L n (λ i → mode (fsuc i)) (λ i → cutoff (fsuc i)) weight)

-- Finite partition function (product-form): factorization into independent modes.

Z-prod
  : ∀ {ℓ ℓM}
    (R : Ring {ℓ})
    (L : SemiringLaws R)
    {Mode : Set ℓM}
  → (n : ℕ)
  → (mode   : Fin n → Mode)
  → (cutoff : Fin n → ℕ)
  → (weight : Mode → Ring.Carrier R)
  → Ring.Carrier R
Z-prod R L zero    mode cutoff weight = Ring.1# R
Z-prod R L (suc n) mode cutoff weight =
  Ring._*_ R
    (sumPow R (weight (mode fzero)) (cutoff fzero))
    (Z-prod R L n (λ i → mode (fsuc i)) (λ i → cutoff (fsuc i)) weight)

Z-sum≡Z-prod
  : ∀ {ℓ ℓM}
    (R : Ring {ℓ})
    (L : SemiringLaws R)
    {Mode : Set ℓM}
    (n : ℕ)
    (mode   : Fin n → Mode)
    (cutoff : Fin n → ℕ)
    (weight : Mode → Ring.Carrier R)
  → Z-sum R L n mode cutoff weight ≡ Z-prod R L n mode cutoff weight
Z-sum≡Z-prod R L zero mode cutoff weight = refl
Z-sum≡Z-prod R L (suc n) mode cutoff weight =
  trans
    (cong (sumPowMul R (weight (mode fzero)) (cutoff fzero))
          (Z-sum≡Z-prod R L n (λ i → mode (fsuc i)) (λ i → cutoff (fsuc i)) weight))
    (sumPowMul≡sumPow*_ {R = R} L (weight (mode fzero)) (cutoff fzero)
      (Z-prod R L n (λ i → mode (fsuc i)) (λ i → cutoff (fsuc i)) weight))
