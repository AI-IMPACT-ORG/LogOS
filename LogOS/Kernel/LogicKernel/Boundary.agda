{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Boundary where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Boundary.IO

open import LogOS.Kernel.LogicKernel

-- Default Boundary I/O view derived from a LogicKernel.

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → BoundaryIO Sig Q (LogicKernel.HWorld K) (LogicKernel.BB K) (LogicKernel.HTruth K)
boundaryIO K = fromKernelShape (LogicKernel.shape K)
