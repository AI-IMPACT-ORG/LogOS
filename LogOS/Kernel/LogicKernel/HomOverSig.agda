{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.HomOverSig where

-- ============================================================================
-- HETEROGENEOUS LOGIC-KERNEL MORPHISMS (OVER A SIGNATURE MAP)
--
-- This is the `LogicKernel` analogue of `LogOS.Kernel.HomOverSig`.
--
-- A `LogicKernelHom` compares kernels over a fixed signature. Using
-- `reindexLogicKernel`, we can compare kernels over different signatures by
-- packaging:
--   - a `SigHom σ`, and
--   - a hom into the pulled-back target.
--
-- Because pullback preserves constraints+code on-the-nose, this is lightweight
-- and aligns S/H/G/R reindexing without forcing a nontrivial `mapCode σ`.
-- ============================================================================

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter

open import LogOS.Algebra.ConAlg

open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.Hom
open import LogOS.Kernel.LogicKernel.Reindex
open import LogOS.Kernel.HomOverSigCore as Core

-- Reindex a logic-kernel hom along a signature map.
--
-- This works because `reindexLogicKernel` preserves constraints and code
-- layers on-the-nose.

reindexLogicKernelHom
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    {K K' : LogicKernel Sig₂ Q}
    → LogicKernelHom K K'
    → LogicKernelHom (reindexLogicKernel σ K) (reindexLogicKernel σ K')
reindexLogicKernelHom σ h = record
  { con-hom    = LogicKernelHom.con-hom h
  ; mapCode    = LogicKernelHom.mapCode h
  ; map-encode = LogicKernelHom.map-encode h
  ; map-decode = LogicKernelHom.map-decode h
  }

-- Coherence morphism: reindexing is functorial up to a canonical `LogicKernelHom`.
--
-- The `LogicKernelHom` notion only cares about constraints+code, so this can be
-- the identity on those layers even if the (S/H) satisfaction packaging differs.

reindexLogicKernel-composeHom
  : ∀ {ℓ : Level} {Sig₁ Sig₂ Sig₃ : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (τ : SigHom Sig₂ Sig₃)
    (K : LogicKernel Sig₃ Q)
  → LogicKernelHom (reindexLogicKernel σ (reindexLogicKernel τ K))
                  (reindexLogicKernel (composeSigHom σ τ) K)
reindexLogicKernel-composeHom σ τ K = record
  { con-hom    = idHom≡ (conAlgOf K)
  ; mapCode    = λ γ → γ
  ; map-encode = λ _ → refl
  ; map-decode = λ _ → refl
  }

module _ {ℓ : Level} {Q : QAdapter ℓ} where
  reindexLogicKernel-idHom
    : ∀ {Sig : LogOSSignature ℓ}
      (K : LogicKernel Sig Q)
    → LogicKernelHom K (reindexLogicKernel (idSigHom Sig) K)
  reindexLogicKernel-idHom K =
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
        { Obj                = λ Sig → LogicKernel Sig Q
        ; Hom                = λ {Sig} → LogicKernelHom {Sig = Sig} {Q = Q}
        ; idHom              = λ {Sig} K → idLogicKernelHom {Sig = Sig} {Q = Q} K
        ; composeHom         = λ {Sig} {K₁} {K₂} {K₃} h₁ h₂ →
                                 composeLogicKernelHom {Sig = Sig} {Q = Q} {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} h₁ h₂
        ; reindexObj         = λ {Sig₁ Sig₂} σ K →
                                 reindexLogicKernel {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ K
        ; reindexHom         = λ {Sig₁ Sig₂} σ {K} {K'} h →
                                 reindexLogicKernelHom {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Q = Q} σ {K = K} {K' = K'} h
        ; reindex-composeHom = λ {Sig₁ Sig₂ Sig₃} σ τ K →
                                 reindexLogicKernel-composeHom {Sig₁ = Sig₁} {Sig₂ = Sig₂} {Sig₃ = Sig₃} {Q = Q} σ τ K
        ; reindex-idHom      = λ {Sig} K → reindexLogicKernel-idHom {Sig = Sig} K
        }

  module C = Core.WithOps ops

  open C public
    renaming
      ( HomOver       to LogicKernelHomOver
      ; idHomOver     to idLogicKernelHomOver
      ; composeHomOver to composeLogicKernelHomOver
      )
