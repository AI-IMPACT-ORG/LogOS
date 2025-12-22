{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Initial.OverSig where

-- ============================================================================
-- INITIALITY THREADED THROUGH SIGNATURE MORPHISMS
--
-- If `FreeK` is initial at `Sig₁`, then for any signature map `σ : SigHom Sig₁ Sig₂`
-- and any kernel `K₂ : Kernel Sig₂ Q`, the pulled-back kernel `reindexKernel σ K₂`
-- receives the unique fold from `FreeK`.
--
-- Packaging that fold together with `σ` yields a heterogeneous morphism
-- `KernelHomOver FreeK K₂`.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter

open import LogOS.Kernel
open import LogOS.Kernel.Reindex
open import LogOS.Algebra.ConAlg
open import LogOS.Kernel.Hom
open import LogOS.Kernel.HomOverSig
open import LogOS.Kernel.Initial

-- Fold into a kernel over a different signature, along a chosen `SigHom`.

foldKOver
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig₁ Q)
    (σ  : SigHom Sig₁ Sig₂)
    (K₂ : Kernel Sig₂ Q)
  → KernelHomOver (InitialKernel.FreeK IK) K₂
foldKOver IK σ K₂ = record
  { σ   = σ
  ; hom = InitialKernel.foldK IK (reindexKernel σ K₂)
  }

-- Uniqueness of folds (specialised).

foldKOver-unique
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig₁ Q)
    (σ  : SigHom Sig₁ Sig₂)
    (K₂ : Kernel Sig₂ Q)
    (h  : KernelHom (InitialKernel.FreeK IK) (reindexKernel σ K₂))
  → (∀ c →
        KernelHom.mapCode (InitialKernel.foldK IK (reindexKernel σ K₂))
          (Kernel.encode (InitialKernel.FreeK IK) c)
        ≡
        KernelHom.mapCode h
          (Kernel.encode (InitialKernel.FreeK IK) c))
    ×
    (∀ d →
        ConAlgHom≡.mapb (KernelHom.con-hom (InitialKernel.foldK IK (reindexKernel σ K₂))) d
        ≡
        ConAlgHom≡.mapb (KernelHom.con-hom h) d)
foldKOver-unique IK σ K₂ h =
  InitialKernel.unique IK (reindexKernel σ K₂) h

foldKOver-unique≃
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig₁ Q)
    (σ  : SigHom Sig₁ Sig₂)
    (K₂ : Kernel Sig₂ Q)
    (h  : KernelHom (InitialKernel.FreeK IK) (reindexKernel σ K₂))
  →
    (∀ γ →
      Kernel.decode (reindexKernel σ K₂)
        (KernelHom.mapCode (InitialKernel.foldK IK (reindexKernel σ K₂)) γ)
      ≡
      ConAlgHom≡.map∂
        (KernelHom.con-hom (InitialKernel.foldK IK (reindexKernel σ K₂)))
        (Kernel.decode (InitialKernel.FreeK IK) γ))
    ×
    (∀ γ →
      Kernel.decode (reindexKernel σ K₂)
        (KernelHom.mapCode h γ)
      ≡
      ConAlgHom≡.map∂ (KernelHom.con-hom h)
        (Kernel.decode (InitialKernel.FreeK IK) γ))
    ×
    (∀ γ →
      Kernel.decode (reindexKernel σ K₂)
        (KernelHom.mapCode (InitialKernel.foldK IK (reindexKernel σ K₂)) γ)
      ≡
      Kernel.decode (reindexKernel σ K₂)
        (KernelHom.mapCode h γ))
foldKOver-unique≃ IK σ K₂ h =
  InitialKernel.unique≃ IK (reindexKernel σ K₂) h

-- Coherence: folding into a doubly-reindexed kernel factors through the
-- canonical reindexing composition morphism.

foldKOver-compose-unique
  : ∀ {ℓ : Level} {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK : InitialKernel Sig₁ Q)
    (σ  : SigHom Sig₁ Sig₂)
    (τ  : SigHom Sig₂ Sig₃)
    (K₃ : Kernel Sig₃ Q)
  → (∀ c →
        KernelHom.mapCode (InitialKernel.foldK IK (reindexKernel (composeSigHom σ τ) K₃))
          (Kernel.encode (InitialKernel.FreeK IK) c)
        ≡
        KernelHom.mapCode
          (composeKernelHom
             (InitialKernel.foldK IK (reindexKernel σ (reindexKernel τ K₃)))
             (reindexKernel-composeHom σ τ K₃))
          (Kernel.encode (InitialKernel.FreeK IK) c))
    ×
    (∀ d →
        ConAlgHom≡.mapb
          (KernelHom.con-hom (InitialKernel.foldK IK (reindexKernel (composeSigHom σ τ) K₃))) d
        ≡
        ConAlgHom≡.mapb
          (KernelHom.con-hom
             (composeKernelHom
                (InitialKernel.foldK IK (reindexKernel σ (reindexKernel τ K₃)))
                (reindexKernel-composeHom σ τ K₃))) d)
foldKOver-compose-unique IK σ τ K₃ =
  InitialKernel.unique IK (reindexKernel (composeSigHom σ τ) K₃) h
  where
    h : KernelHom (InitialKernel.FreeK IK) (reindexKernel (composeSigHom σ τ) K₃)
    h =
      composeKernelHom
        (InitialKernel.foldK IK (reindexKernel σ (reindexKernel τ K₃)))
        (reindexKernel-composeHom σ τ K₃)

-- Specialisation: the “initial kernel assignment” respects composition of
-- signature maps up to the initiality uniqueness notion.

initial→initial
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK₁ : InitialKernel Sig₁ Q)
    (σ   : SigHom Sig₁ Sig₂)
    (IK₂ : InitialKernel Sig₂ Q)
  → KernelHomOver (InitialKernel.FreeK IK₁) (InitialKernel.FreeK IK₂)
initial→initial IK₁ σ IK₂ = foldKOver IK₁ σ (InitialKernel.FreeK IK₂)

initial→initial-compose-unique
  : ∀ {ℓ : Level} {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (IK₁ : InitialKernel Sig₁ Q)
    (IK₂ : InitialKernel Sig₂ Q)
    (IK₃ : InitialKernel Sig₃ Q)
    (σ   : SigHom Sig₁ Sig₂)
    (τ   : SigHom Sig₂ Sig₃)
  →
    (∀ c →
      KernelHom.mapCode
        (KernelHomOver.hom (initial→initial IK₁ (composeSigHom σ τ) IK₃))
        (Kernel.encode (InitialKernel.FreeK IK₁) c)
      ≡
      KernelHom.mapCode
        (KernelHomOver.hom (composeKernelHomOver (initial→initial IK₁ σ IK₂) (initial→initial IK₂ τ IK₃)))
        (Kernel.encode (InitialKernel.FreeK IK₁) c))
    ×
    (∀ d →
      ConAlgHom≡.mapb
        (KernelHom.con-hom (KernelHomOver.hom (initial→initial IK₁ (composeSigHom σ τ) IK₃))) d
      ≡
      ConAlgHom≡.mapb
        (KernelHom.con-hom (KernelHomOver.hom (composeKernelHomOver (initial→initial IK₁ σ IK₂) (initial→initial IK₂ τ IK₃)))) d)
initial→initial-compose-unique IK₁ IK₂ IK₃ σ τ =
  InitialKernel.unique IK₁
    (reindexKernel (composeSigHom σ τ) (InitialKernel.FreeK IK₃))
    (KernelHomOver.hom (composeKernelHomOver (initial→initial IK₁ σ IK₂) (initial→initial IK₂ τ IK₃)))
