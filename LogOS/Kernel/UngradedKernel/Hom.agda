{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Hom where

open import LogOS.Prelude

open import LogOS.Kernel.UngradedKernel
open import LogOS.Kernel.Shape as Core hiding (FlowCode)
open import LogOS.Kernel.UngradedKernel.ConAlgOf public using (conAlgOf)
open import LogOS.Kernel.HomCore as HomCore
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.ConAlg
open import LogOS.Minimal.Truth as Truth

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  private
    ops : HomCore.Ops {ℓ}
    ops =
      record
        { Obj          = UngradedKernel Sig Q
        ; conAlgOf     = conAlgOf
        ; Code         = UngradedKernel.Code
        ; encode       = UngradedKernel.encode
        ; decode       = UngradedKernel.decode
        ; reify        = UngradedKernel.reify
        ; reify-decode = UngradedKernel.reify-decode
        ; Body         = UngradedKernel.Body
        ; Body∂        = UngradedKernel.Body∂
        ; body-decode  = UngradedKernel.body-decode
        }

  open HomCore.WithOps ops public
    renaming
      ( Hom              to UngradedKernelHom
      ; idHom            to idUngradedKernelHom
      ; composeHom       to composeUngradedKernelHom
      ; map∂-id          to map∂-id
      ; map∂-compose     to map∂-compose
      ; mapCode-id       to mapCode-id
      ; mapCode-compose  to mapCode-compose
      ; map-reify-decode to map-reify-decode
      ; map-body-decode  to map-body-decode
      )

-- Optional strengthening: preservation of Flow on boundary constraints.

record UngradedKernelHomFlow {ℓ : Level}
                             {Sig : LogOSSignature ℓ}
                             {Q : QAdapter ℓ}
                             (K₁ K₂ : UngradedKernel Sig Q)
                             (h : UngradedKernelHom K₁ K₂)
                             : Set (lsuc (lsuc ℓ)) where
  open UngradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
  open UngradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
  open UngradedKernelHom h
  field
    flow-hom
      : Truth.GuardedCore.FlowHom
          (BulkBoundary.bnd BB₁)
          (BulkBoundary.bnd BB₂)
          G₁ G₂
          (ConAlgHom≡.map∂ con-hom)

-- Optional strengthening: Flow preservation + transport of `Th*`.

record UngradedKernelHomFlowStable {ℓ : Level}
                                   {Sig : LogOSSignature ℓ}
                                   {Q : QAdapter ℓ}
                                   (K₁ K₂ : UngradedKernel Sig Q)
                                   (h : UngradedKernelHom K₁ K₂)
                                   : Set (lsuc (lsuc ℓ)) where
  open UngradedKernel K₁ renaming (BB to BB₁; GTruth to G₁)
  open UngradedKernel K₂ renaming (BB to BB₂; GTruth to G₂)
  open UngradedKernelHom h
  field
    stable-hom
      : Truth.GuardedCore.FlowHomStable
          (BulkBoundary.bnd BB₁)
          (BulkBoundary.bnd BB₂)
          G₁ G₂
          (ConAlgHom≡.map∂ con-hom)

  open Truth.GuardedCore.FlowHomStable stable-hom public

ungradedKernelHomFlowOfStable
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : UngradedKernel Sig Q}
    {h : UngradedKernelHom K₁ K₂}
  → UngradedKernelHomFlowStable K₁ K₂ h
  → UngradedKernelHomFlow K₁ K₂ h
ungradedKernelHomFlowOfStable hf =
  record { flow-hom = UngradedKernelHomFlowStable.flow-hom hf }

-- Convenience: build a stable-flow structure from a plain flow-hom + a Th* witness.

stableOfFlow+Th
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : UngradedKernel Sig Q}
    {h : UngradedKernelHom K₁ K₂}
  → UngradedKernelHomFlow K₁ K₂ h
  → (preserves-Th : ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K₂))
                    (ConAlgHom≡.map∂ (UngradedKernelHom.con-hom h)
                      (Truth.GuardedCore.GuardedClosure.Th* (UngradedKernel.GTruth K₁)))
                    (Truth.GuardedCore.GuardedClosure.Th* (UngradedKernel.GTruth K₂)))
  → UngradedKernelHomFlowStable K₁ K₂ h
stableOfFlow+Th hf preserves-Th =
  record
    { stable-hom =
        record
          { flow-hom     = UngradedKernelHomFlow.flow-hom hf
          ; preserves-Th = preserves-Th
          }
    }
