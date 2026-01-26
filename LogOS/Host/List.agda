{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.List where

-- Bridge to Agda built-in lists to avoid duplicate BUILTIN bindings.

open import LogOS.Host.Level using (Level)
open import Agda.Builtin.List public

-- Small utilities (kept minimal; extend only when duplication appears).

map : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : ∀ {ℓA} {A : Set ℓA} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {ℓA} {A : Set ℓA} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

zipWith
  : ∀ {ℓA ℓB ℓC}
    {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
  → (A → B → C) → List A → List B → List C
zipWith f []       []       = []
zipWith f []       (_ ∷ _)  = []
zipWith f (_ ∷ _)  []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

