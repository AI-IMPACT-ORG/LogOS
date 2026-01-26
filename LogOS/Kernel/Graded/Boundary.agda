{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Boundary where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Boundary.IO
open import LogOS.Kernel.Graded

-- Default Boundary I/O view derived from a GradedKernel.

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → BoundaryIO Sig Q (GradedKernel.HWorld K) (GradedKernel.BB K) (GradedKernel.HTruth K)
boundaryIO K = fromKernelShape (GradedKernel.shape K)
