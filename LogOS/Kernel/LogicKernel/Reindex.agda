{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
-- - keeps the guarded tier (`GTier`) unchanged (it acts on the same boundary preorder).
--
-- This is the minimal “tier alignment” story over signatures: S/H/G/R (reflection)
-- can be pulled back uniformly without introducing new axioms.
--
-- A stronger variant with explicit strict-formula translation is provided by
-- `reindexLogicKernelWithFml`.
-- ============================================================================

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; ↔-refl)

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.ReindexCore using
  ( reindexKernelShape
  ; reindexKernelShapeWithFml
  ; reindexKernelShapeLaws
  ; reindexKernelShapeLawsWithFml
  )
open import LogOS.Kernel.LogicKernel

reindexLogicKernel
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → LogicKernel Sig₂ Q
    → LogicKernel Sig₁ Q
reindexLogicKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K₂ =
  record
    { shape        = reindexKernelShape σ (LogicKernel.shape K₂)
    ; shapeLaws   = reindexKernelShapeLaws σ (LogicKernel.shape K₂) (LogicKernel.shapeLaws K₂)
    ; G           = LogicKernel.G K₂
    ; guard-decode = LogicKernel.guard-decode K₂
    ; decode-γ*    = LogicKernel.decode-γ* K₂
    }

-- Reindex a logic kernel along a signature map with an explicit formula translation.
reindexLogicKernelWithFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : LogicKernel Sig₂ Q)
    {Fml₁ : Set ℓ}
  → (Fml₁ → LogicKernel.Fml K)
  → LogicKernel Sig₁ Q
reindexLogicKernelWithFml σ K mapFml =
  record
    { shape        = reindexKernelShapeWithFml σ (LogicKernel.shape K) mapFml
    ; shapeLaws   = reindexKernelShapeLawsWithFml σ (LogicKernel.shape K) mapFml (LogicKernel.shapeLaws K)
    ; G           = LogicKernel.G K
    ; guard-decode = LogicKernel.guard-decode K
    ; decode-γ*    = LogicKernel.decode-γ* K
    }

reindexLogic-sat-bnd
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : LogicKernel Sig₂ Q)
  → ∀ p c
  → LogicKernel.Sat_H_bnd (reindexLogicKernel σ K) p c
    ↔ LogicKernel.Sat_H_bnd K (SigHom.map∂Cosp σ p) c
reindexLogic-sat-bnd _ _ _ _ = ↔-refl

reindexLogic-satS-withFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : LogicKernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → LogicKernel.Fml K)
  → ∀ w φ
  → Truth.StrictTruth.StrictLayer.Sat_S (LogicKernel.Strict (reindexLogicKernelWithFml σ K mapFml)) w φ
    ↔ Truth.StrictTruth.StrictLayer.Sat_S (LogicKernel.Strict K) (SigHom.mapCosp σ w) (mapFml φ)
reindexLogic-satS-withFml _ _ _ _ _ = ↔-refl
