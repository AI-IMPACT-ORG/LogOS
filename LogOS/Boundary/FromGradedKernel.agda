{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.FromGradedKernel where

-- Default Boundary I/O view derived from a GradedKernel.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.IO using (BoundaryIO; fromKernelShape)
import LogOS.Kernel.Graded as GK

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GK.GradedKernel Sig Q)
  → BoundaryIO Sig Q (GK.GradedKernel.HWorld K) (GK.GradedKernel.BB K) (GK.GradedKernel.HTruth K)
boundaryIO K = fromKernelShape (GK.GradedKernel.shape K)

