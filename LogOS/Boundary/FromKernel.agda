{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.FromKernel where

-- Default Boundary I/O view derived from a Kernel.
--
-- This lives at the Boundary layer (not the Kernel layer) so the Kernel stays
-- free of boundary dependencies, per the README architecture diagram.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.IO using (BoundaryIO; fromKernelShape)
import LogOS.Kernel as LK

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LK.Kernel Sig Q)
  → BoundaryIO Sig Q (LK.Kernel.HWorld K) (LK.Kernel.BB K) (LK.Kernel.HTruth K)
boundaryIO K = fromKernelShape (LK.Kernel.shape K)

