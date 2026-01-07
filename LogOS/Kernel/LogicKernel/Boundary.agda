{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Boundary where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO

open import LogOS.Kernel.LogicKernel

-- Default Boundary I/O view derived from a LogicKernel.

boundaryIO
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → BoundaryIO Sig Q (LogicKernel.HWorld K) (LogicKernel.BB K) (LogicKernel.HTruth K)
boundaryIO {Sig = Sig} {Q = Q} K =
  record
    { to∂    = to∂Sig
    ; from∂  = from∂Sig
    ; Sat∂   = LogicKernel.Sat_H_bnd K
    ; sat-coh = LogicKernel.sat-coh K
    }
  where
  open LogOSSignature Sig renaming (to∂ to to∂Sig; from∂ to from∂Sig)

