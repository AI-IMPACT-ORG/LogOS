{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.ConAlg
open import LogOS.Kernel
open import LogOS.Kernel.ConAlgOf public using (conAlgOf)
open import LogOS.Kernel.HomCore as HomCore
import LogOS.Kernel.HomFlowShared as FlowShared
open import LogOS.Minimal.Truth as Truth
import LogOS.Kernel.GuardedTier as GuardedTier

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : HomCore.Ops {ℓ}
    ops =
      record
        { Obj          = Kernel Sig Q
        ; conAlgOf     = conAlgOf
        ; Code         = Kernel.Code
        ; encode       = Kernel.encode
        ; decode       = Kernel.decode
        ; reify        = Kernel.reify
        ; reify-decode = Kernel.reify-decode
        ; Body         = Kernel.Body
        ; Body∂        = Kernel.Body∂
        ; body-decode  = Kernel.body-decode
        }

  open HomCore.WithOps ops public
    renaming
      ( Hom              to KernelHom
      ; idHom            to idKernelHom
      ; composeHom       to composeKernelHom
      ; map∂-id          to map∂-id
      ; map∂-compose     to map∂-compose
      ; mapCode-id       to mapCode-id
      ; mapCode-compose  to mapCode-compose
      ; map-reify-decode to map-reify-decode
      ; map-body-decode  to map-body-decode
      )

  map∂Of : ∀ {K₁ K₂ : Kernel Sig Q}
         → KernelHom K₁ K₂
         → ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₁))
         → ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K₂))
  map∂Of h = ConAlgHom≡.map∂ (KernelHom.con-hom h)

  -- Optional strengthening: preservation of the saturation flow on boundary
  -- constraints (lax). This is the ungraded “flow homomorphism” interface,
  -- instantiated at `GTier.sat`.

  private
    module GT = Truth.GuardedCore {ℓ = ℓ}

    satClosure : (K : Kernel Sig Q) → GT.GuardedClosure (BulkBoundary.bnd (Kernel.BB K))
    satClosure K = GuardedTier.toGuardedClosure (Kernel.G K)

    module FlowCore = FlowShared.With
      (Kernel Sig Q)
      Kernel.BB
      satClosure
      KernelHom
      map∂Of

  KernelHomFlow = FlowCore.HomFlow
  module KernelHomFlow = FlowCore.HomFlow

  KernelHomFlowStable = FlowCore.HomFlowStable
  module KernelHomFlowStable = FlowCore.HomFlowStable

  kernelHomFlowOfStable
    : ∀ {K₁ K₂ : Kernel Sig Q} {h : KernelHom K₁ K₂}
    → KernelHomFlowStable K₁ K₂ h
    → KernelHomFlow K₁ K₂ h
  kernelHomFlowOfStable = FlowCore.homFlowOfStable

  -- Decode-level transport for the saturation modality on code (`Box`).

  map-box-decode≤
    : ∀ {K₁ K₂ : Kernel Sig Q}
      {h : KernelHom K₁ K₂}
      (hf : KernelHomFlow K₁ K₂ h)
      (γ : Kernel.Code K₁)
    → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
        (Kernel.decode K₂ (KernelHom.mapCode h (Box K₁ γ)))
        (Kernel.decode K₂ (Box K₂ (KernelHom.mapCode h γ)))
  map-box-decode≤ {K₁ = K₁} {K₂ = K₂} {h = h} hf γ =
    let
      CP₂ = BulkBoundary.bnd (Kernel.BB K₂)

      open KernelHom h
      open GT.FlowHom (KernelHomFlow.flow-hom hf) using (preserves-F)

      Flow₁ = GTier.Flow (Kernel.G K₁) (GTier.sat (Kernel.G K₁))
      Flow₂ = GTier.Flow (Kernel.G K₂) (GTier.sat (Kernel.G K₂))
      map∂  = ConAlgHom≡.map∂ con-hom

      eqL : Kernel.decode K₂ (mapCode (Box K₁ γ))
            ≡ map∂ (Flow₁ (Kernel.decode K₁ γ))
      eqL =
        trans
          (map-decode (Box K₁ γ))
          (cong map∂ (decode-Box K₁ γ))

      eqR : Kernel.decode K₂ (mapCode γ)
            ≡ map∂ (Kernel.decode K₁ γ)
      eqR = map-decode γ

      step : ConPreorder._⊑_ CP₂
               (map∂ (Flow₁ (Kernel.decode K₁ γ)))
               (Flow₂ (Kernel.decode K₂ (mapCode γ)))
      step =
        subst
          (λ y →
            ConPreorder._⊑_ CP₂
              (map∂ (Flow₁ (Kernel.decode K₁ γ)))
              (Flow₂ y))
          (sym eqR)
          (preserves-F (Kernel.decode K₁ γ))
    in
    subst
      (λ x →
        ConPreorder._⊑_ CP₂ x
          (Kernel.decode K₂ (Box K₂ (mapCode γ))))
      (sym eqL)
      (subst
        (λ y →
          ConPreorder._⊑_ CP₂
            (map∂ (Flow₁ (Kernel.decode K₁ γ)))
            y)
        (sym (decode-Box K₂ (mapCode γ)))
        step)
