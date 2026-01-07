{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Reindex where

-- ============================================================================
-- LOGIC-KERNEL REINDEXING (PULLBACK) ALONG SIGNATURE MORPHISMS
--
-- This is the `LogicKernel` analogue of `LogOS.Kernel.Reindex`:
-- - contravariant in `SigHom`,
-- - reindexes the world/satisfaction indices,
-- - preserves constraints and code on-the-nose,
-- - keeps the guarded tier (`GTier`) unchanged (it acts on the same boundary poset).
--
-- This is the minimal “tier alignment” story over signatures: S/H/G/R (reflection)
-- can be pulled back uniformly without introducing new axioms.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.ReindexCore using (reindexKernelShape)
open import LogOS.Kernel.LogicKernel

reindexLogicKernel
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → LogicKernel Sig₂ Q
    → LogicKernel Sig₁ Q
reindexLogicKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K₂ =
  record
    { shape        = reindexKernelShape σ (LogicKernel.shape K₂)
    ; G           = LogicKernel.G K₂
    ; guard-decode = LogicKernel.guard-decode K₂
    ; decode-γ*    = LogicKernel.decode-γ* K₂
    }
