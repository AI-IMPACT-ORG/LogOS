{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.Utils where

open import LogOS.Prelude

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)

-- Small utilities ------------------------------------------------------------

infix 4 _==ℕ_ _≤?ℕ_
infixl 6 _∸_
infix 0 if_then_else_

_==ℕ_ : ℕ → ℕ → Bool
zero  ==ℕ zero   = true
zero  ==ℕ suc _  = false
suc _ ==ℕ zero   = false
suc m ==ℕ suc n  = m ==ℕ n

_≤?ℕ_ : ℕ → ℕ → Bool
zero  ≤?ℕ _      = true
suc _ ≤?ℕ zero   = false
suc m ≤?ℕ suc n  = m ≤?ℕ n

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

_∸_ : ℕ → ℕ → ℕ
zero  ∸ _      = zero
suc m ∸ zero   = suc m
suc m ∸ suc n  = m ∸ n

lookupDefault : ∀ {A : Set} → A → List A → ℕ → A
lookupDefault d []       _        = d
lookupDefault d (x ∷ xs) zero     = x
lookupDefault d (x ∷ xs) (suc i)  = lookupDefault d xs i
