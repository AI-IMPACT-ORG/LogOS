{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Infinite.Adapters where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Infinite

-- Small convenience shims: reuse theorem APIs that take `po/ωCPO/FF` separately
-- by projecting them from an `InfiniteKernel`.

KernelPO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (IK : InfiniteKernel Sig Q)
  → BulkBoundaryPO (Kernel.BB (InfiniteKernel.K IK))
KernelPO IK = InfiniteKernel.po IK

OmegaCPO∂
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (IK : InfiniteKernel Sig Q)
  → (let module GT∞ = Truth.GuardedTruth Sig Q in GT∞.OmegaCPO)
      (BulkBoundary.bnd (Kernel.BB (InfiniteKernel.K IK)))
OmegaCPO∂ IK = InfiniteKernel.ωCPO IK

FiniteFirst∂
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → (IK : InfiniteKernel Sig Q)
  → (let module GT∞ = Truth.GuardedTruth Sig Q in GT∞.FiniteFirst)
      (BulkBoundary.bnd (Kernel.BB (InfiniteKernel.K IK)))
      (Kernel.GTruth (InfiniteKernel.K IK))
      (InfiniteKernel.ωCPO IK)
FiniteFirst∂ IK = InfiniteKernel.FF IK
