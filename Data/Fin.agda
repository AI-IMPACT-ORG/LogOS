{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Fin where

open import Data.Nat using (ℕ; zero; suc)

-- Finite indices: `Fin n` has exactly n inhabitants.
data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc  : ∀ {n} → Fin n → Fin (suc n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ {suc _} fzero    = zero
toℕ {suc _} (fsuc i) = suc (toℕ i)

