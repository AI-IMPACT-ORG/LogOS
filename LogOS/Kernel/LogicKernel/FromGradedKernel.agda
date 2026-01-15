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
open import LogOS.Kernel.Graded
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.GuardedTier as GT

GTier-of-GradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GTier Q (BulkBoundary.bnd (GradedKernel.BB K))
GTier-of-GradedKernel K =
  GT.fromGradedClosure (GradedKernel.GTruth K) (GradedKernel.step-grade K)

asLogicKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → LogicKernel Sig Q
asLogicKernel K =
  record
    { shape       = GradedKernel.shape K
    ; shapeLaws   = GradedKernel.shapeLaws K
    ; G           = GTier-of-GradedKernel K
    ; guard-decode = GradedKernel.guard-decode K
    ; decode-γ*    = GradedKernel.decode-γ* K
    }
