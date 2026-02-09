{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.InfoTheory.Shannon.Facts where

open import LogOS.Prelude hiding (_+_; _*_)

open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude.Fin using (Fin)

-- A “facts pack” for finite Shannon information theory:
-- it isolates analytic commitments (carrier, ln/exp, inequalities) as explicit fields.
--
-- Smell fix: this is intentionally *not* a single “god record”.
-- We split the interface into smaller sub-records (carrier/order/sums/positivity/…)
-- and then assemble the usual one-stop `ShannonFacts` by re-exporting each part.

record Carrier : Set₁ where
  infixl 6 _+_
  infixl 7 _*_
  infix  8 -_
  field
    ℝ   : Set
    0#  : ℝ
    1#  : ℝ
    _+_ : ℝ → ℝ → ℝ
    _*_ : ℝ → ℝ → ℝ
    -_  : ℝ → ℝ

    *-idr : ∀ x → (x * 1#) ≡ x
    -- (Minimal: only the unit law used by derived theorems in this pack.)

record Order (C : Carrier) : Set₁ where
  open Carrier C
  infix 4 _≤_
  field
    _≤_     : ℝ → ℝ → Set
    ≤-refl  : ∀ {x} → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

record FiniteSum (C : Carrier) (O : Order C) : Set₁ where
  open Carrier C
  open Order O
  field
    sum : ∀ {n : ℕ} → (Fin n → ℝ) → ℝ
    sum0 : ∀ {n : ℕ} → sum (λ (_ : Fin n) → 0#) ≡ 0#

    sum-cong : ∀ {n : ℕ} {f g : Fin n → ℝ} → (∀ i → f i ≡ g i) → sum f ≡ sum g
    sum-+     : ∀ {n : ℕ} (f g : Fin n → ℝ) → sum (λ i → f i + g i) ≡ (sum f + sum g)
    sum-*ˡ    : ∀ {n : ℕ} (c : ℝ) (f : Fin n → ℝ) → sum (λ i → c * f i) ≡ c * sum f
    sum-mono  : ∀ {n : ℕ} {f g : Fin n → ℝ} → (∀ i → f i ≤ g i) → sum f ≤ sum g

    sum-swap
      : ∀ {m n : ℕ}
        (f : Fin m → Fin n → ℝ)
      → sum (λ i → sum (f i)) ≡ sum (λ j → sum (λ i → f i j))

record Positivity (C : Carrier) (O : Order C) : Set₁ where
  open Carrier C
  open Order O
  field
    Pos    : ℝ → Set
    Pos→≤0     : ∀ {x} → Pos x → 0# ≤ x
    ≤0-*       : ∀ {x y} → 0# ≤ x → 0# ≤ y → 0# ≤ (x * y)
    Pos-*      : ∀ {x y} → Pos x → Pos y → Pos (x * y)

record FiniteSumPos (C : Carrier) (O : Order C) (S : FiniteSum C O) (P : Positivity C O) : Set₁ where
  open Carrier C
  open Order O
  open FiniteSum S
  open Positivity P
  field
    -- Finite-sum positivity: needed to show strict channels preserve full support.
    sumPos : ∀ {n : ℕ} (f : Fin n → ℝ) → (∀ i → Pos (f i)) → Pos (sum f)

record KLTerm (C : Carrier) {O : Order C} (P : Positivity C O) : Set₁ where
  open Carrier C
  open Order O
  open Positivity P
  field
    -- Total “KL term” with a 0-extension convention.
    klTerm : ℝ → ℝ → ℝ
    klTerm0≤ : ∀ {b} → 0# ≤ b → klTerm 0# b ≡ 0#
    klTerm11≡0 : klTerm 1# 1# ≡ 0#

record LogSumIneq
  (C : Carrier)
  (O : Order C)
  (S : FiniteSum C O)
  (P : Positivity C O)
  (K : KLTerm C {O = O} P)
  : Set₁ where
  open Carrier C
  open Order O
  open FiniteSum S
  open Positivity P
  open KLTerm K
  field
    logSumIneq
      : ∀ {n : ℕ} (a b : Fin n → ℝ)
      → (∀ i → 0# ≤ a i)
      → (∀ i → Pos (b i))
      → klTerm (sum a) (sum b) ≤ sum (λ i → klTerm (a i) (b i))

-- Assemble the full Shannon facts pack by composing smaller interfaces.
record ShannonFacts : Set₁ where
  field
    car        : Carrier
    ord        : Order car
    sumPack    : FiniteSum car ord
    posPack    : Positivity car ord
    sumPosPack : FiniteSumPos car ord sumPack posPack
    klPack     : KLTerm car {O = ord} posPack
    logSumPack : LogSumIneq car ord sumPack posPack klPack

  open Carrier car public
  open Order ord public
  open FiniteSum sumPack public
  open Positivity posPack public
  open FiniteSumPos sumPosPack public
  open KLTerm klPack public
  open LogSumIneq logSumPack public
