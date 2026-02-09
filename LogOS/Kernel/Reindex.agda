{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Reindex where

-- ============================================================================
-- KERNEL REINDEXING (PULLBACK) ALONG SIGNATURE MORPHISMS
--
-- This is the `Kernel`-level reindexing story:
-- - contravariant in `SigHom`,
-- - reindexes the world/satisfaction indices,
-- - preserves constraints and code on-the-nose,
-- - keeps the guarded tier (`GTier`) unchanged (it acts on the same boundary preorder).
--
-- This is the minimal “tier alignment” story over signatures: S/H/G/R (reflection)
-- can be pulled back uniformly without introducing new axioms.
--
-- A stronger variant with explicit strict-formula translation is provided by
-- `reindexKernelWithFml`.
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
open import LogOS.Kernel

reindexKernel
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    → SigHom Sig₁ Sig₂
    → Kernel Sig₂ Q
    → Kernel Sig₁ Q
reindexKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K₂ =
  record
    { shape        = reindexKernelShape σ (Kernel.shape K₂)
    ; shapeLaws   = reindexKernelShapeLaws σ (Kernel.shape K₂) (Kernel.shapeLaws K₂)
    ; G           = Kernel.G K₂
    ; guard-decode = Kernel.guard-decode K₂
    ; decode-γ*    = Kernel.decode-γ* K₂
    }

-- Reindex a logic kernel along a signature map with an explicit formula translation.
reindexKernelWithFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
  → (Fml₁ → Kernel.Fml K)
  → Kernel Sig₁ Q
reindexKernelWithFml σ K mapFml =
  record
    { shape        = reindexKernelShapeWithFml σ (Kernel.shape K) mapFml
    ; shapeLaws   = reindexKernelShapeLawsWithFml σ (Kernel.shape K) mapFml (Kernel.shapeLaws K)
    ; G           = Kernel.G K
    ; guard-decode = Kernel.guard-decode K
    ; decode-γ*    = Kernel.decode-γ* K
    }

-- The lightweight reindexing preserves the code carrier and decoding map
-- definitionally (only world indices are changed).

reindex-Code
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → Kernel.Code (reindexKernel σ K) ≡ Kernel.Code K
reindex-Code _ _ = refl

reindex-decode
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → ∀ γ → Kernel.decode (reindexKernel σ K) γ ≡ Kernel.decode K γ
reindex-decode _ _ _ = refl

reindex-FlowCode
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → ∀ γ → FlowCode (reindexKernel σ K) γ ≡ FlowCode K γ
reindex-FlowCode _ _ _ = refl

reindexWithFml-Code
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → Kernel.Code (reindexKernelWithFml σ K mapFml) ≡ Kernel.Code K
reindexWithFml-Code _ _ _ = refl

reindexWithFml-decode
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → ∀ γ → Kernel.decode (reindexKernelWithFml σ K mapFml) γ ≡ Kernel.decode K γ
reindexWithFml-decode _ _ _ _ = refl

reindexWithFml-FlowCode
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → ∀ γ → FlowCode (reindexKernelWithFml σ K mapFml) γ ≡ FlowCode K γ
reindexWithFml-FlowCode _ _ _ _ = refl

reindexLogic-sat-bnd
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → ∀ p c
  → Kernel.Sat_H_bnd (reindexKernel σ K) p c
    ↔ Kernel.Sat_H_bnd K (SigHom.map∂Cosp σ p) c
reindexLogic-sat-bnd _ _ _ _ = ↔-refl

reindexLogic-satS-withFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → ∀ w φ
  → Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict (reindexKernelWithFml σ K mapFml)) w φ
    ↔ Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) (SigHom.mapCosp σ w) (mapFml φ)
reindexLogic-satS-withFml _ _ _ _ _ = ↔-refl
