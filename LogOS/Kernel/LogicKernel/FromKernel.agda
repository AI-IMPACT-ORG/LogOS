{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.FromKernel where

-- Instance bridge: any (unguarded) `Kernel` yields a `LogicKernel` by taking
-- `Step = ⊤` and ignoring the step index.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.GuardedTier as GT

GTier-of-Kernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → GTier Q (BulkBoundary.bnd (Kernel.BB K))
GTier-of-Kernel K = GT.fromGuardedClosure (Kernel.GTruth K)

asLogicKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → LogicKernel Sig Q
asLogicKernel K =
  record
    { shape       = Kernel.shape K
    ; shapeLaws   = record
        { decode∘encode = Kernel.decode∘encode K
        ; γ*-guard      = Kernel.γ*-guard K
        ; reify-decode  = Kernel.reify-decode K
        ; body-decode   = Kernel.body-decode K
        }
    ; G           = GTier-of-Kernel K
    ; guard-decode = Kernel.guard-decode K
    ; decode-γ*    = Kernel.decode-γ* K
    }
