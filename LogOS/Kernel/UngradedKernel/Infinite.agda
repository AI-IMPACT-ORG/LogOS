{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Infinite where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalOps)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.UngradedKernel

-- “Infinite kernel”: a kernel whose boundary constraints carry ω-chain structure
-- and a finite-first/continuity story for the guarded Flow.
--
-- This is intentionally a *companion record* rather than changing `UngradedKernel`
-- itself, so existing finite kernels and tests remain valid.

record InfiniteKernel {ℓ : Level}
                      (Sig : LogOSSignature ℓ)
                      (Q   : QAdapter ℓ)
                      : Set (lsuc (lsuc ℓ)) where
  private
    module GT∞ = Truth.GuardedTruth Sig Q

  field
    K   : UngradedKernel Sig Q

  open UngradedKernel K public

  field
    po   : BulkBoundaryPO BB

    ωCPO : GT∞.OmegaCPO (BulkBoundary.bnd BB)
    FF   : GT∞.FiniteFirst (BulkBoundary.bnd BB) GTruth ωCPO

    -- Canonical choice for the ω-CPO bottom: align ⊥ with the boundary monoidal unit.
    -- This is what lets the initial kernel’s fold produce a Flow-preserving hom
    -- automatically for any InfiniteKernel target (no extra per-target assumptions).
    bot≡I∂
      : GT∞.OmegaCPO.⊥ ωCPO
        ≡ (MonoidalOps.I MBnd)

-- Convenience projections.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    module GT∞ = Truth.GuardedTruth Sig Q

  KernelPO
    : (IK : InfiniteKernel Sig Q)
    → BulkBoundaryPO (UngradedKernel.BB (InfiniteKernel.K IK))
  KernelPO IK = InfiniteKernel.po IK

  OmegaCPO∂
    : (IK : InfiniteKernel Sig Q)
    → GT∞.OmegaCPO (BulkBoundary.bnd (UngradedKernel.BB (InfiniteKernel.K IK)))
  OmegaCPO∂ IK = InfiniteKernel.ωCPO IK

  FiniteFirst∂
    : (IK : InfiniteKernel Sig Q)
    → GT∞.FiniteFirst
        (BulkBoundary.bnd (UngradedKernel.BB (InfiniteKernel.K IK)))
        (UngradedKernel.GTruth (InfiniteKernel.K IK))
        (InfiniteKernel.ωCPO IK)
  FiniteFirst∂ IK = InfiniteKernel.FF IK
