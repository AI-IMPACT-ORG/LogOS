{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
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
open import LogOS.Kernel.HomOverSigCore as Core

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

module _ {ℓ : Level} {Q : QAdapter ℓ} where
  reindexKernel-idHom
    : ∀ {Sig : LogOSSignature ℓ}
      (K : Kernel Sig Q)
    → KernelHom K (reindexKernel (idSigHom Sig) K)
  reindexKernel-idHom K =
    record
      { con-hom    = idHom≡ (conAlgOf K)
      ; mapCode    = λ γ → γ
      ; map-encode = λ _ → refl
      ; map-decode = λ _ → refl
      }

  private
    ops : Core.Ops {ℓ}
    ops =
      record
        { Obj                = λ Sig → Kernel Sig Q
        ; Hom                = λ {Sig} → KernelHom {Sig = Sig} {Q = Q}
        ; idHom              = λ {Sig} K → idKernelHom {Sig = Sig} {Q = Q} K
        ; composeHom         = λ {Sig} {K₁} {K₂} {K₃} h₁ h₂ →
                                 composeKernelHom {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} h₁ h₂
        ; reindexObj         = λ {Sig₁ Sig₂} σ K →
                                 reindexKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K
        ; reindexHom         = λ {Sig₁ Sig₂} σ {K} {K'} h →
                                 reindexKernelHom {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ {K = K} {K' = K'} h
        ; reindex-composeHom = λ {Sig₁ Sig₂ Sig₃} σ τ K →
                                 reindexKernel-composeHom {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Sig₃ = Sig₃} {Q = Q} σ τ K
        ; reindex-idHom      = λ {Sig} K → reindexKernel-idHom {Sig = Sig} K
        }

  module C = Core.WithOps ops

  open C public
    renaming
      ( HomOver       to KernelHomOver
      ; idHomOver     to idKernelHomOver
      ; composeHomOver to composeKernelHomOver
      )
