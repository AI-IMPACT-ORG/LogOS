{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Boundary where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Boundary.IO
open import LogOS.Kernel

-- Default Boundary I/O view derived from a Kernel.

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → BoundaryIO Sig Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
boundaryIO K = fromKernelShape (Kernel.shape K)
