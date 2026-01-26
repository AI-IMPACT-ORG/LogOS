{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Infinite where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded

-- “Infinite graded kernel”: a graded kernel whose boundary constraints carry ω-chain
-- structure and a finite-first/continuity story for the *saturation* Flow.
--
-- This mirrors `LogOS.Kernel.Infinite` for ungraded kernels, but uses
-- `forgetGradedClosure` at the saturation grade (cost → ∞).

record InfiniteGradedKernel {ℓ : Level}
                            (Sig : LogOSSignature ℓ)
                            (Q   : QAdapter ℓ)
                            : Set (lsuc (lsuc ℓ)) where
  private
    module GT∞ = Truth.GuardedCore

  field
    K : GradedKernel Sig Q

  open GradedKernel K public

  field
    po   : BulkBoundaryPO BB -- ANTISYM-OK

    ωCPO : GT∞.OmegaCPO (BulkBoundary.bnd BB)
    FF   : GT∞.FiniteFirst
            (BulkBoundary.bnd BB)
            (GT∞.forgetGradedClosure GTruth)
            ωCPO

    -- Canonical choice for the ω-CPO bottom: align ⊥ with the boundary monoidal unit.
    bot≡I∂
      : GT∞.OmegaCPO.⊥ ωCPO
        ≡ (MonoidalOps.I MBnd)

-- Convenience projections (shape matches the ungraded `InfiniteKernel` API).

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    module GT∞ = Truth.GuardedCore

  KernelPO
    : (IK : InfiniteGradedKernel Sig Q)
    → BulkBoundaryPO (GradedKernel.BB (InfiniteGradedKernel.K IK)) -- ANTISYM-OK
  KernelPO IK = InfiniteGradedKernel.po IK

  OmegaCPO∂
    : (IK : InfiniteGradedKernel Sig Q)
    → GT∞.OmegaCPO (BulkBoundary.bnd (GradedKernel.BB (InfiniteGradedKernel.K IK)))
  OmegaCPO∂ IK = InfiniteGradedKernel.ωCPO IK

  FiniteFirst∂
    : (IK : InfiniteGradedKernel Sig Q)
    → GT∞.FiniteFirst
        (BulkBoundary.bnd (GradedKernel.BB (InfiniteGradedKernel.K IK)))
        (GT∞.forgetGradedClosure (GradedKernel.GTruth (InfiniteGradedKernel.K IK)))
        (InfiniteGradedKernel.ωCPO IK)
  FiniteFirst∂ IK = InfiniteGradedKernel.FF IK

