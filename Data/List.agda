{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.List where

-- Bridge to Agda built-in lists to avoid duplicate BUILTIN bindings.

open import Level using (Level)
open import Agda.Builtin.List public

-- Small utilities (kept minimal; extend only when duplication appears).

map : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
