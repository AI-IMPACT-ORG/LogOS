{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.QuoteConeMMP.ClosureKernelMMPImpl where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Derived: any guarded closure yields an MMP on its canonical quote kernel.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; _≈_
  ; ≈-refl
  )
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.LOG.ArchitectureQuote2Cat using
  ( quoteKernel
  ; quoteEncodePort
  )
import LogOS.LT.Theorems.Centering as Centering

import LogOS.LT.Theorems.QuoteConeMMP.QuotationConeImpl as QuotationConeImpl

module ClosureKernelMMP
  {ℓCon ℓRel : Level}
  {CP : ConPreorder ℓCon ℓRel}
  (GC₀ : GuardedClosure CP)
  where

  K : Kernel ℓCon ℓRel (lsuc (ℓCon ⊔ ℓRel))
  K = quoteKernel GC₀

  module QC = QuotationConeImpl.QuotationCone K GC₀

  canonical : QC.QuoteWitness
  canonical =
    record
      { EK = quoteEncodePort GC₀
      ; decode-encode≈Flow = λ c → ≈-refl CP (GuardedClosure.Flow GC₀ c)
      }

  fiber : Centering.ContractibleFiber QC.QuoteWitness QC._≈R_
  fiber = QC.fiber canonical
