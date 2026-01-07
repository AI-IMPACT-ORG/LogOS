{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Infinite.Reindex where

-- ============================================================================
-- REINDEXING FOR INFINITE KERNELS
--
-- The infinite-kernel companion structure is also reindexable along a
-- signature morphism, because its extra fields live purely over the boundary
-- constraint poset (independent of the concrete world/satisfaction indices).
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Adjunction using (MonoidalPoset)
open import LogOS.Kernel
open import LogOS.Kernel.Reindex
open import LogOS.Kernel.Infinite

reindexInfiniteKernel
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → InfiniteKernel Sig₂ Q
    → InfiniteKernel Sig₁ Q
reindexInfiniteKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ IK₂ =
  record
    { K = K₁
    ; po = InfiniteKernel.po IK₂
    ; ωCPO = record
        { ⊥     = GT₂.OmegaCPO.⊥ ωCPO₂
        ; isBot = GT₂.OmegaCPO.isBot ωCPO₂
        ; supω  = GT₂.OmegaCPO.supω ωCPO₂
        ; ub    = GT₂.OmegaCPO.ub ωCPO₂
        ; least = GT₂.OmegaCPO.least ωCPO₂
        }
    ; FF = record
        { approx0   = GT₂.FiniteFirst.approx0 FF₂
        ; approxS   = GT₂.FiniteFirst.approxS FF₂
        ; base      = GT₂.FiniteFirst.base FF₂
        ; step      = GT₂.FiniteFirst.step FF₂
        ; Th⋆-as-sup = GT₂.FiniteFirst.Th⋆-as-sup FF₂
        ; cont-ω    = GT₂.FiniteFirst.cont-ω FF₂
        }
    ; bot≡I∂ = InfiniteKernel.bot≡I∂ IK₂
    }
  where
    K₁ : Kernel Sig₁ Q
    K₁ = reindexKernel σ (InfiniteKernel.K IK₂)

    module GT₂ = Truth.GuardedTruth Sig₂ Q

    ωCPO₂ : GT₂.OmegaCPO (BulkBoundary.bnd (Kernel.BB (InfiniteKernel.K IK₂)))
    ωCPO₂ = InfiniteKernel.ωCPO IK₂

    FF₂
      : GT₂.FiniteFirst
          (BulkBoundary.bnd (Kernel.BB (InfiniteKernel.K IK₂)))
          (Kernel.GTruth (InfiniteKernel.K IK₂))
          ωCPO₂
    FF₂ = InfiniteKernel.FF IK₂
