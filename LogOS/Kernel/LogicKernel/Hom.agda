{-
LogOS: an Agda research library for foundational logic system architecture.
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
