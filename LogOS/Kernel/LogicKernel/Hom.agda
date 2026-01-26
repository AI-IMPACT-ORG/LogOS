{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Hom where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Algebra.ConAlg
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.ConAlgOf public using (conAlgOf)
open import LogOS.Kernel.HomCore as HomCore

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : HomCore.Ops {ℓ}
    ops =
      record
        { Obj          = LogicKernel Sig Q
        ; conAlgOf     = conAlgOf
        ; Code         = LogicKernel.Code
        ; encode       = LogicKernel.encode
        ; decode       = LogicKernel.decode
        ; reify        = LogicKernel.reify
        ; reify-decode = LogicKernel.reify-decode
        ; Body         = LogicKernel.Body
        ; Body∂        = LogicKernel.Body∂
        ; body-decode  = LogicKernel.body-decode
        }

  open HomCore.WithOps ops public
    renaming
      ( Hom              to LogicKernelHom
      ; idHom            to idLogicKernelHom
      ; composeHom       to composeLogicKernelHom
      ; map-reify-decode to map-reify-decode
      ; map-body-decode  to map-body-decode
      )

  map∂-id
    : ∀ {K} (c : ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K)))
    → ConAlgHom≡.map∂ (LogicKernelHom.con-hom (idLogicKernelHom K)) c ≡ c
  map∂-id _ = refl

  map∂-compose
    : ∀ {K₁ K₂ K₃}
      (h₁ : LogicKernelHom K₁ K₂)
      (h₂ : LogicKernelHom K₂ K₃)
      (c : ConPreorder.Con (BulkBoundary.bnd (LogicKernel.BB K₁)))
    → ConAlgHom≡.map∂ (LogicKernelHom.con-hom (composeLogicKernelHom h₁ h₂)) c
      ≡ ConAlgHom≡.map∂ (LogicKernelHom.con-hom h₂)
          (ConAlgHom≡.map∂ (LogicKernelHom.con-hom h₁) c)
  map∂-compose _ _ _ = refl

  mapCode-id
    : ∀ {K} (γ : LogicKernel.Code K)
    → LogicKernelHom.mapCode (idLogicKernelHom K) γ ≡ γ
  mapCode-id _ = refl

  mapCode-compose
    : ∀ {K₁ K₂ K₃}
      (h₁ : LogicKernelHom K₁ K₂)
      (h₂ : LogicKernelHom K₂ K₃)
      (γ : LogicKernel.Code K₁)
    → LogicKernelHom.mapCode (composeLogicKernelHom h₁ h₂) γ
      ≡ LogicKernelHom.mapCode h₂ (LogicKernelHom.mapCode h₁ γ)
  mapCode-compose _ _ _ = refl
