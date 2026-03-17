{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.List.Ops where

-- Minimal, stdlib-independent list utilities.
--
-- Keep `LogOS.Prelude.List` minimal (just the `List` type); collect small
-- derived operations here so downstream packs can reuse them without
-- re-defining append/map/etc in multiple places.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

infixr 6 _++_
_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → List A → List B
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → List B) → List A → List B
concatMap _ [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

-- Membership (for small “almost everywhere” laws, restricted products, ...).
data _∈_ {ℓ} {A : Set ℓ} (a : A) : List A → Set ℓ where
  here  : ∀ {xs} → a ∈ (a ∷ xs)
  there : ∀ {x xs} → a ∈ xs → a ∈ (x ∷ xs)

infix 4 _∈_

infix 4 _∉_
_∉_ : ∀ {ℓ} {A : Set ℓ} → A → List A → Set ℓ
a ∉ xs = ¬ (a ∈ xs)

∈-++-l
  : ∀ {ℓ} {A : Set ℓ} {a : A} {xs ys : List A}
  → a ∈ xs → a ∈ (xs ++ ys)
∈-++-l {xs = []} ()
∈-++-l {xs = _ ∷ _} here = here
∈-++-l {xs = _ ∷ _} (there p) = there (∈-++-l p)

∈-++-r
  : ∀ {ℓ} {A : Set ℓ} {a : A} {xs ys : List A}
  → a ∈ ys → a ∈ (xs ++ ys)
∈-++-r {xs = []} p = p
∈-++-r {xs = _ ∷ _} p = there (∈-++-r p)

∉-++-l
  : ∀ {ℓ} {A : Set ℓ} {a : A} {xs ys : List A}
  → a ∉ (xs ++ ys) → a ∉ xs
∉-++-l notin p = notin (∈-++-l p)

∉-++-r
  : ∀ {ℓ} {A : Set ℓ} {a : A} {xs ys : List A}
  → a ∉ (xs ++ ys) → a ∉ ys
∉-++-r notin p = notin (∈-++-r p)
