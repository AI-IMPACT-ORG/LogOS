{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.CompressionValuation where

-- Quantitative interpretation of finite compression counts.
--
-- This is the minimal count-level valuation surface used by the current
-- observational Landauer bridge: a finite loss count is interpreted in a
-- chosen cost scale, monotonically and compatibly with the ambient
-- join-prequantale multiplication/unit. The bridge therefore calibrates
-- explicit count loss into the same refinement-first quantitative surface used
-- by Landauer bounds.

open import LogOS.Prelude
open import LogOS.Prelude.Nat.Order using (_≤ℕ_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)

record CompressionValuation
  {ℓScaleCon ℓScaleRel : Level}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  (JP : JoinPrequantale Scale)
  : Set (lsuc (ℓScaleCon ⊔ ℓScaleRel)) where
  field
    countValue : ℕ → Con Scale
    countValue-mono : ∀ {m n} → m ≤ℕ n → _⊑_ Scale (countValue m) (countValue n)
    countValue-zero≈e : _≈_ Scale (countValue zero) (JoinPrequantale.e JP)
    countValue-+≈·
      : ∀ m n
      → _≈_ Scale
          (countValue (m + n))
          (JoinPrequantale._·_ JP (countValue m) (countValue n))

open CompressionValuation public

singleCompression
  : ∀ {ℓScaleCon ℓScaleRel : Level}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  → CompressionValuation JP
  → Con Scale
singleCompression V = countValue V (suc zero)

singleCompression≤countValue
  : ∀ {ℓScaleCon ℓScaleRel : Level}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
  → (V : CompressionValuation JP)
  → ∀ {n}
  → suc zero ≤ℕ n
  → _⊑_ Scale (singleCompression V) (countValue V n)
singleCompression≤countValue V =
  countValue-mono V
