{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.FlowUniversality where

open import LogOS.Prelude

open import LogOS.Kernel.Graded
open import LogOS.Computation.Core
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Prelude as Eq using (sym)

open import LogOS.Domain.Universality.ComplexitySpectrum
open import LogOS.Domain.Universality.Core

-- Universality claim for the flow operator: any step semantics can be
-- embedded into a Kernel’s derived code-level flow (`FlowCode`) via an encoding that intertwines steps.

record FlowUniversal {ℓ : Level}
                          (Sig : LogOS.Base.Signature.LogOSSignature ℓ)
                          (Q   : LogOS.Minimal.Adapter.QAdapter ℓ)
                          (K   : GradedKernel Sig Q)
                          {ℓc : Level}
                          (CodeSrc : Set ℓc)
                          (CompSrc : Computation {ℓc} CodeSrc)
                          : Set (lsuc (ℓ ⊔ ℓc)) where
  open GradedKernel K
  open Computation CompSrc
  field
    encode     : CodeSrc → Code
    intertwine : ∀ c → FlowCode K (encode c) ≡ encode (Computation.Step CompSrc c)
