{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Relation.Binary.PropositionalEquality where

-- Host wrapper around Agda.Builtin.Equality (≡) with basic combinators.
--
-- Provides `_≡_`, `refl`, and small helpers (`sym`, `trans`, `cong`, `subst`, ...),
-- without depending on agda-stdlib.

open import Agda.Builtin.Equality  using (_≡_; refl) public

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (f : A → B → C) {x y : A} {u v : B}
  → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
  → (P : A → Set ℓ₂) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

-- Transport along a composed equality is the same as transporting in steps.
subst-trans
  : ∀ {ℓA ℓP}
    {A : Set ℓA}
    (P : A → Set ℓP)
    {x y z : A}
  → (p : x ≡ y)
  → (q : y ≡ z)
  → (u : P x)
  → subst P (trans p q) u ≡ subst P q (subst P p u)
subst-trans P refl refl u = refl

-- Transport out-and-back cancels.
subst-sym-inv
  : ∀ {ℓA ℓP}
    {A : Set ℓA}
    (P : A → Set ℓP)
    {x y : A}
  → (p : x ≡ y)
  → (u : P x)
  → subst P (sym p) (subst P p u) ≡ u
subst-sym-inv P refl u = refl
