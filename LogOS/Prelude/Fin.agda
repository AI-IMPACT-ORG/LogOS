{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.Fin where

-- Minimal bounded finite indices and a few structural helpers.
--
-- This is intentionally stdlib-free and small: enough for explicit finitary
-- presentations (finite supports, compression witnesses, bounded lookup).

open import LogOS.Host.Level using (Level; lzero)
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.Host.Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import LogOS.Host.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Host.Empty using (⊥)

infix 4 _≢_

data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc  : ∀ {n} → Fin n → Fin (suc n)

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = x ≡ y → ⊥ {lzero}

inject₁ : ∀ {n} → Fin n → Fin (suc n)
inject₁ = fsuc

fsuc-injective : ∀ {n} {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
fsuc-injective refl = refl

finEq : ∀ {n} → (i j : Fin n) → (i ≡ j) ⊎ (i ≢ j)
finEq {suc n} fzero fzero = inj₁ refl
finEq {suc n} fzero (fsuc j) = inj₂ (λ ())
finEq {suc n} (fsuc i) fzero = inj₂ (λ ())
finEq {suc n} (fsuc i) (fsuc j) with finEq i j
... | inj₁ eq = inj₁ (cong fsuc eq)
... | inj₂ neq = inj₂ (λ eq → neq (fsuc-injective eq))

-- Insert an index into `Fin (suc n)` while skipping the chosen hole.
raiseExcept : ∀ {n} → (hole : Fin (suc n)) → Fin n → Fin (suc n)
raiseExcept fzero i = fsuc i
raiseExcept (fsuc hole) fzero = fzero
raiseExcept (fsuc hole) (fsuc i) = fsuc (raiseExcept hole i)

raiseExcept-≢ : ∀ {n} (hole : Fin (suc n)) (i : Fin n) → raiseExcept hole i ≢ hole
raiseExcept-≢ fzero i ()
raiseExcept-≢ (fsuc hole) fzero ()
raiseExcept-≢ (fsuc hole) (fsuc i) eq =
  raiseExcept-≢ hole i (fsuc-injective eq)

-- Remove a chosen hole from `Fin (suc n)`, given evidence that we are not at
-- the hole.
lowerFromDiff
  : ∀ {n}
  → (hole : Fin (suc n))
  → (i : Fin (suc n))
  → i ≢ hole
  → Fin n
lowerFromDiff fzero fzero neq with neq refl
... | ()
lowerFromDiff fzero (fsuc i) neq = i
lowerFromDiff {n = suc n} (fsuc hole) fzero neq = fzero
lowerFromDiff {n = suc n} (fsuc hole) (fsuc i) neq =
  fsuc (lowerFromDiff hole i (λ eq → neq (cong fsuc eq)))

lowerFromDiff-cong
  : ∀ {n}
  → (hole : Fin (suc n))
  → {x y : Fin (suc n)}
  → (eq : x ≡ y)
  → (x≢hole : x ≢ hole)
  → (y≢hole : y ≢ hole)
  → lowerFromDiff hole x x≢hole ≡ lowerFromDiff hole y y≢hole
lowerFromDiff-cong fzero {x = fzero} {y = fzero} eq x≢hole y≢hole with x≢hole refl
... | ()
lowerFromDiff-cong fzero {x = fzero} {y = fsuc y} () x≢hole y≢hole
lowerFromDiff-cong fzero {x = fsuc x} {y = fzero} () x≢hole y≢hole
lowerFromDiff-cong fzero {x = fsuc x} {y = fsuc y} eq x≢hole y≢hole =
  fsuc-injective eq
lowerFromDiff-cong {n = suc n} (fsuc hole) {x = fzero} {y = fzero} eq x≢hole y≢hole = refl
lowerFromDiff-cong (fsuc hole) {x = fzero} {y = fsuc y} () x≢hole y≢hole
lowerFromDiff-cong (fsuc hole) {x = fsuc x} {y = fzero} () x≢hole y≢hole
lowerFromDiff-cong {n = suc n} (fsuc hole) {x = fsuc x} {y = fsuc y} eq x≢hole y≢hole =
  cong
    fsuc
    (lowerFromDiff-cong
      hole
      (fsuc-injective eq)
      (λ p → x≢hole (cong fsuc p))
      (λ p → y≢hole (cong fsuc p)))

lowerFromDiff-raiseExcept
  : ∀ {n}
  → (hole : Fin (suc n))
  → (i : Fin n)
  → lowerFromDiff hole (raiseExcept hole i) (raiseExcept-≢ hole i) ≡ i
lowerFromDiff-raiseExcept fzero i = refl
lowerFromDiff-raiseExcept (fsuc hole) fzero = refl
lowerFromDiff-raiseExcept (fsuc hole) (fsuc i) =
  cong
    fsuc
    (trans
      (lowerFromDiff-cong
        hole
        refl
        (λ eq → raiseExcept-≢ (fsuc hole) (fsuc i) (cong fsuc eq))
        (raiseExcept-≢ hole i))
      (lowerFromDiff-raiseExcept hole i))
