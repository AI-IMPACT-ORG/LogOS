{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Examples.InfoRouteChainIR where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Graded

open import LogOS.Domain.UniversalIR.Core using (UCode)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.UniversalIRCM as UIR
import LogOS.Domain.Complexity.Examples.InfoRouteChain as Chain

-- Example instantiation shell: UniversalIR inputs + a kernel embedding.
-- This is still conditional on a graded kernel and a code embedding,
-- but fixes the computation model to a chosen UniversalIR brand.

module For
  {Sig : LogOSSignature lzero}
  {Q : QAdapter lzero}
  (K : GradedKernel Sig Q)
  (toCodeK : UCode → GradedKernel.Code K)
  (fromCodeK : GradedKernel.Code K → UCode)
  (gradeBound : ℕ → QAdapter.Scale Q)
  (Pℕ : PolyPred)
  (brand : UIR.Brand)
  where

  M : UIR.StandardCMᴵᴿ {ℓ = lzero}
  M = UIR.mkIRCM Pℕ brand

  open UIR.StandardCMᴵᴿ M renaming
    ( Input  to Inputᵀ
    ; size   to sizeᵀ
    ; poly   to polyᵀ
    ; wsize  to wsizeᵀ
    )

  module TR = UIR.TR K toCodeK fromCodeK gradeBound M

  WSize : GradedKernel.Code K → ℕ
  WSize w = wsizeᵀ (fromCodeK w)

  module C = Chain.ForFromNat
    K Inputᵀ sizeᵀ
    TR.DetRun TR.VerRun TR.VerRunWith
    gradeBound Pℕ

  -- Concrete size→grade map for the NonDegenerate guard in this instantiation.
  sizeGrade : ℕ → QAdapter.Scale Q
  sizeGrade = gradeBound

  module WithAccExample {ℓA} (Acc : C.R.Con → Set ℓA) where
    module W = C.WithAcc Acc

    NonDegenerateAt : W.O.LOB → Set _
    NonDegenerateAt lob = W.NonDegenerate lob sizeGrade

  open C public
