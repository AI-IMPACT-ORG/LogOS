{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.FromUngradedKernel where

-- Instance bridge: any `UngradedKernel` yields a (CHL-facing) `Kernel` by taking
-- `Step = ⊤` and ignoring the step index.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con

import LogOS.Kernel.UngradedKernel as UK
open import LogOS.Kernel
open import LogOS.Kernel.GuardedTier as GT

GTier-of-UngradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UK.UngradedKernel Sig Q)
  → GTier Q (BulkBoundary.bnd (UK.UngradedKernel.BB K))
GTier-of-UngradedKernel K = GT.fromGuardedClosure (UK.UngradedKernel.GTruth K)

asKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : UK.UngradedKernel Sig Q)
  → Kernel Sig Q
asKernel K =
  record
    { shape        = UK.UngradedKernel.shape K
    ; shapeLaws    = UK.UngradedKernel.shapeLaws K
    ; G            = GTier-of-UngradedKernel K
    ; guard-decode = UK.UngradedKernel.guard-decode K
    ; decode-γ*    = UK.UngradedKernel.decode-γ* K
    }
