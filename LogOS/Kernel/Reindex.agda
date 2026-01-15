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
--
-- A stronger, syntax-translation variant is available as `reindexKernelWithFml`.
-- ============================================================================

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; ↔-refl)

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.ReindexCore public using
  ( reindexWorldH
  ; reindexKernelShape
  ; reindexKernelShapeWithFml
  ; reindexKernelShapeLaws
  ; reindexKernelShapeLawsWithFml
  ; reindexKernelLaws
  ; reindexKernelLawsWithFml
  )

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
    ; laws         = reindexKernelLaws σ (Kernel.shape K₂) (Kernel.GTruth K₂) (Kernel.laws K₂)
    }

-- Reindex a kernel along a signature map with an explicit formula translation.
--
-- This keeps constraints and code on-the-nose, but replaces the strict layer
-- with `Fml₁` and interprets it through `mapFml` into the original kernel.

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
    ; GTruth       = Kernel.GTruth K
    ; laws         = reindexKernelLawsWithFml σ (Kernel.shape K) (Kernel.GTruth K) mapFml (Kernel.laws K)
    }

-- Reindexing preserves the code layer on-the-nose.

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
  → ∀ gamma
  → Kernel.decode (reindexKernel σ K) gamma ≡ Kernel.decode K gamma
reindex-decode _ _ _ = refl

reindex-sat-bnd
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → ∀ p c
  → Kernel.Sat_H_bnd (reindexKernel σ K) p c
    ↔ Kernel.Sat_H_bnd K (SigHom.map∂Cosp σ p) c
reindex-sat-bnd _ _ _ _ = ↔-refl

reindex-satS-withFml
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → ∀ w φ
  → Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict (reindexKernelWithFml σ K mapFml)) w φ
    ↔ Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K) (SigHom.mapCosp σ w) (mapFml φ)
reindex-satS-withFml _ _ _ _ _ = ↔-refl

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
  → ∀ gamma
  → Kernel.decode (reindexKernelWithFml σ K mapFml) gamma ≡ Kernel.decode K gamma
reindexWithFml-decode _ _ _ _ = refl

reindexWithFml-FlowCode
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
    (mapFml : Fml₁ → Kernel.Fml K)
  → ∀ gamma
  → FlowCode (reindexKernelWithFml σ K mapFml) gamma ≡ FlowCode K gamma
reindexWithFml-FlowCode _ _ _ _ = refl

reindex-FlowCode
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → ∀ gamma
  → FlowCode (reindexKernel σ K) gamma ≡ FlowCode K gamma
reindex-FlowCode _ _ _ = refl
