{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.FromGradedKernel where

-- Instance bridge: any `GradedKernel` yields a `LogicKernel` by taking
-- `Step = Scale` and using the graded saturation step `sat`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.Graded
open import LogOS.Kernel.LogicKernel

private
  module GC = Truth.GuardedCore

GTier-of-GradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GTier Q (BulkBoundary.bnd (GradedKernel.BB K))
GTier-of-GradedKernel {Q = Q} K =
  record
    { Step      = QAdapter.Scale Q
    ; step      = GradedKernel.step-grade K
    ; sat       = GradedClosure.sat (GradedKernel.GTruth K)
    ; Flow      = GradedClosure.Flow (GradedKernel.GTruth K)
    ; mono      = GradedClosure.mono (GradedKernel.GTruth K)
    ; infl-sat  = GradedClosure.infl-sat (GradedKernel.GTruth K)
    ; idemp-sat = GradedClosure.idemp-sat (GradedKernel.GTruth K)
    ; Th*       = GradedClosure.Th* (GradedKernel.GTruth K)
    ; Th*-fixed = GradedClosure.Th*-fixed (GradedKernel.GTruth K)
    }

asLogicKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → LogicKernel Sig Q
asLogicKernel K =
  record
    { shape       = GradedKernel.shape K
    ; G           = GTier-of-GradedKernel K
    ; guard-decode = GradedKernel.guard-decode K
    ; decode-γ*    = GradedKernel.decode-γ* K
    }

