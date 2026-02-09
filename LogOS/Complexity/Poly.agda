{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.Poly where

open import LogOS.Prelude
open import LogOS.Complexity.Arithmetic

-- A minimal polynomial predicate: at least the family n^k is declared polynomial.

record PolyPred : Set₁ where
  field
    isPoly     : (ℕ → ℕ) → Set
    -- Identity bound is polynomial (needed by many TruthRoute targets).
    id-isPoly  : isPoly (λ n → n)
    pow-isPoly : ∀ k → isPoly (λ n → pow k n)
