{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Kernel2CatGraded where

-- Graded analogue of `LogOS.Theorems.CategoryTheory.Kernel2Cat` (interface only).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
import LogOS.Kernel.Graded.Hom2Cat as KH₂
open import LogOS.Theorems.CategoryTheory.WrapperCore public
  renaming (Ref2Cat to GradedKernel2Cat)

GradedKernel2Cat-instance
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  → GradedKernel2Cat Sig Q
GradedKernel2Cat-instance Sig Q =
  RelThin2Cat→Ref2CatCore (KH₂.GradedKernelRelThin2Cat {Sig = Sig} {Q = Q})
