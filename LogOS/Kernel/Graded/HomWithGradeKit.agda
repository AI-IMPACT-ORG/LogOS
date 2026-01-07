{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.HomWithGradeKit where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Algebra.ConAlg
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.ConAlgOf
open import LogOS.Kernel.HomWithGradeCore as HomWithGradeCore

-- Canonical `HomWithGradeCore` instantiation for graded kernels (over a fixed signature).

module ForSig {ℓ : Level} (Sig : LogOSSignature ℓ) where
  private
    module GT = Truth.GuardedCore

  opsWG : HomWithGradeCore.Ops {ℓ}
  opsWG =
    record
      { Obj             = λ Q → GradedKernel Sig Q
      ; conAlgOf        = conAlgOf
      ; Code            = GradedKernel.Code
      ; encode          = GradedKernel.encode
      ; decode          = GradedKernel.decode
      ; reify           = GradedKernel.reify
      ; reify-decode    = GradedKernel.reify-decode
      ; Body            = GradedKernel.Body
      ; Body∂           = GradedKernel.Body∂
      ; body-decode     = GradedKernel.body-decode
      ; GradeHom        = GT.GradeHom
      ; idGradeHom      = GT.idGradeHom
      ; composeGradeHom = GT.composeGradeHom
      }

  module Core = HomWithGradeCore.WithOps opsWG

