{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Quantum.Measurement where

open import LogOS.Prelude

-- Generic binary-measurement algebra, parameterized by a scalar + state type.
-- This isolates the axioms needed to interpret collapse and normalization.

record BinaryMeasurementLaws
  {ℓS ℓA : Level}
  (Scalar : Set ℓA)
  (_+_ : Scalar → Scalar → Scalar)
  (one : Scalar)
  (State : Set ℓS)
  : Set (lsuc (ℓS ⊔ ℓA)) where
  field
    prob0 prob1 : State → Scalar
    norm        : State → Scalar
    collapse0   : State → State
    collapse1   : State → State

    split-prob
      : ∀ ψ → prob0 ψ + prob1 ψ ≡ norm ψ

    collapse0-norm
      : ∀ ψ → norm (collapse0 ψ) ≡ one

    collapse1-norm
      : ∀ ψ → norm (collapse1 ψ) ≡ one
