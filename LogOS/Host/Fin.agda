{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Fin where

open import LogOS.Host.Nat using (ℕ; zero; suc)

-- Finite indices: `Fin n` has exactly n inhabitants.
data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc  : ∀ {n} → Fin n → Fin (suc n)

toℕ : ∀ {n} → Fin n → ℕ
toℕ {suc _} fzero    = zero
toℕ {suc _} (fsuc i) = suc (toℕ i)

