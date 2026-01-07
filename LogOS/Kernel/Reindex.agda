{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Reindex where

-- ============================================================================
-- KERNEL REINDEXING (PULLBACK) ALONG SIGNATURE MORPHISMS
--
-- Given a structure-preserving signature map `σ : SigHom Sig₁ Sig₂`, we can
-- pull back any `Kernel Sig₂ Q` to a `Kernel Sig₁ Q` by precomposing all
-- world- and satisfaction-indexed fields along `σ`.
--
-- This is designed to be *non-breaking*: it adds reindexing as a new feature
-- without changing the existing `Kernel` record or any existing models.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.ReindexCore public using (reindexWorldH; reindexKernelShape)

-- Reindex a kernel along a signature map.
--
-- Note: This is a lightweight signature morphism story: it preserves formulas,
-- constraints, and code, and only reindexes the observation/world indices.

reindexKernel
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → Kernel Sig₂ Q
    → Kernel Sig₁ Q
reindexKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K₂ =
  record
    { shape        = reindexKernelShape σ (Kernel.shape K₂)
    ; GTruth       = Kernel.GTruth K₂
    ; guard-decode = Kernel.guard-decode K₂
    ; decode-γ*    = Kernel.decode-γ* K₂
    }
