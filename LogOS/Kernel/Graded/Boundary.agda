{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Boundary where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO
open import LogOS.Kernel.Graded

-- Default Boundary I/O view derived from a GradedKernel.

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → BoundaryIO Sig Q (GradedKernel.HWorld K) (GradedKernel.BB K) (GradedKernel.HTruth K)
boundaryIO {Sig = Sig} {Q = Q} K =
  record
    { to∂    = bnd
    ; from∂  = ext
    ; Sat∂   = GradedKernel.Sat_H_bnd K
    ; sat-coh = GradedKernel.sat-coh K
    }
  where
  open LogOSSignature Sig

