{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.HomOverSig where

-- ============================================================================
-- HETEROGENEOUS KERNEL MORPHISMS (OVER A SIGNATURE MAP)
--
-- A `KernelHom` only compares kernels over the *same* signature.
-- Using `reindexKernel`, we can define a lightweight notion of morphism
-- between kernels over different signatures: a signature map plus a kernel
-- homomorphism into the pulled-back target kernel.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Reindex
open import LogOS.Kernel.Hom
open import LogOS.Algebra.ConAlg

-- Reindex a kernel hom along a signature map.
--
-- This works because `reindexKernel` preserves the constraint algebra and code
-- layers on-the-nose.

reindexKernelHom
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    {K K' : Kernel Sig₂ Q}
    → KernelHom K K' → KernelHom (reindexKernel σ K) (reindexKernel σ K')
reindexKernelHom σ h = record
  { con-hom    = KernelHom.con-hom h
  ; mapCode    = KernelHom.mapCode h
  ; map-encode = KernelHom.map-encode h
  ; map-decode = KernelHom.map-decode h
  }

-- Coherence morphism: reindexing is functorial up to a canonical `KernelHom`.
--
-- The kernel-hom notion only cares about constraints+code, so this can be the
-- identity on those layers even if the (S/H) satisfaction packaging differs.

reindexKernel-composeHom
  : ∀ {ℓ : Level} {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (τ : SigHom Sig₂ Sig₃)
    (K : Kernel Sig₃ Q)
    → KernelHom (reindexKernel σ (reindexKernel τ K))
                (reindexKernel (composeSigHom σ τ) K)
reindexKernel-composeHom σ τ K = record
  { con-hom    = idHom≡ (conAlgOf K)
  ; mapCode    = λ γ → γ
  ; map-encode = λ c → refl
  ; map-decode = λ γ → refl
  }

-- Signature-indexed kernel morphism.

record KernelHomOver {ℓ : Level}
                     {Q : QAdapter ℓ}
                     {Sig₁ Sig₂ : LogOSSignature ℓ}
                     (K₁ : Kernel Sig₁ Q)
                     (K₂ : Kernel Sig₂ Q)
                     : Set (lsuc (lsuc ℓ)) where
  field
    σ   : SigHom Sig₁ Sig₂
    hom : KernelHom K₁ (reindexKernel σ K₂)

idKernelHomOver
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    → KernelHomOver K K
idKernelHomOver {Sig = Sig} K = record
  { σ   = idSigHom Sig
  ; hom = idKernelHom K
  }

composeKernelHomOver
  : ∀ {ℓ : Level} {Q : QAdapter ℓ}
    {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ}
    {K₁ : Kernel Sig₁ Q} {K₂ : Kernel Sig₂ Q} {K₃ : Kernel Sig₃ Q}
    → KernelHomOver K₁ K₂ → KernelHomOver K₂ K₃ → KernelHomOver K₁ K₃
composeKernelHomOver {K₂ = K₂} {K₃ = K₃} h₁₂ h₂₃ = record
  { σ   = composeSigHom σ₁₂ σ₂₃
  ; hom = composeKernelHom hom₁₂ (composeKernelHom hom₂₃' bridge)
  }
  where
    open KernelHomOver h₁₂ renaming (σ to σ₁₂; hom to hom₁₂)
    open KernelHomOver h₂₃ renaming (σ to σ₂₃; hom to hom₂₃)

    hom₂₃' : KernelHom (reindexKernel σ₁₂ K₂) (reindexKernel σ₁₂ (reindexKernel σ₂₃ K₃))
    hom₂₃' = reindexKernelHom σ₁₂ hom₂₃

    bridge : KernelHom (reindexKernel σ₁₂ (reindexKernel σ₂₃ K₃))
                     (reindexKernel (composeSigHom σ₁₂ σ₂₃) K₃)
    bridge = reindexKernel-composeHom σ₁₂ σ₂₃ K₃
