{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Infinite where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction using (MonoidalPoset)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel

-- “Infinite kernel”: a kernel whose boundary constraints carry ω-chain structure
-- and a finite-first/continuity story for the guarded Flow.
--
-- This is intentionally a *companion record* rather than changing `Kernel`
-- itself, so existing finite kernels and tests remain valid.

record InfiniteKernel {ℓ : Level}
                      (Sig : LogOSSignature ℓ)
                      (Q   : QAdapter ℓ)
                      : Set (lsuc (lsuc ℓ)) where
  field
    K   : Kernel Sig Q

  open Kernel K public

  field
    po   : BulkBoundaryPO BB

    ωCPO : (let module GT∞ = Truth.GuardedTruth Sig Q in GT∞.OmegaCPO) (BulkBoundary.bnd BB)
    FF   : (let module GT∞ = Truth.GuardedTruth Sig Q in GT∞.FiniteFirst) (BulkBoundary.bnd BB) GTruth ωCPO

    -- Canonical choice for the ω-CPO bottom: align ⊥ with the boundary monoidal unit.
    -- This is what lets the initial kernel’s fold produce a Flow-preserving hom
    -- automatically for any InfiniteKernel target (no extra per-target assumptions).
    bot≡I∂
      : (let module GT∞ = Truth.GuardedTruth Sig Q in GT∞.OmegaCPO.⊥ ωCPO)
        ≡ (MonoidalPoset.I MBnd)
