{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.DiagonalTX where

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- Minimal diagonal truncated-operator specification (purely schematic).
-- Keeps the finite index type P, the local diagonal predicate a₁, and the
-- truncated determinant zero predicate ΛXZero, together with the two bridge
-- lemmas needed by GRH diagonal adapters.

record DiagonalTX {ℓTX}
                  (RS : RiemannSpectral)
                  : Set (lsuc (ℓTX ⊔ lzero)) where
  open RiemannSpectral RS
  field
    P : Set ℓTX
    a₁ : P → Spectral → Set ℓTX
    ΛXZero : Spectral → Set ℓTX

    det-zero→∃local1
      : ∀ s → ΛXZero s → Σ P (λ p → a₁ p s)

    local1→OnLine
      : ∀ s → Σ P (λ p → a₁ p s) → OnLine s
