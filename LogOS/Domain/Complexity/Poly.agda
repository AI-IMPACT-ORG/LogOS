{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Poly where

open import LogOS.Prelude
open import LogOS.Domain.Complexity.Arithmetic

-- A minimal polynomial predicate: at least the family n^k is declared polynomial.

record PolyPred : Set₁ where
  field
    isPoly     : (ℕ → ℕ) → Set
    -- Identity bound is polynomial (needed by many TruthRoute targets).
    id-isPoly  : isPoly (λ n → n)
    pow-isPoly : ∀ k → isPoly (λ n → pow k n)
