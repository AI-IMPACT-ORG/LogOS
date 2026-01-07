{-
LogOS: an Agda research library for foundational logic system architecture.
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
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.LogicKernel

private
  module GC = Truth.GuardedCore

GTier-of-Kernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → GTier Q (BulkBoundary.bnd (Kernel.BB K))
GTier-of-Kernel {Sig = Sig} {Q = Q} K =
  record
    { Step      = Topℓ
    ; step      = ttℓ
    ; sat       = ttℓ
    ; Flow      = λ _ c → GC.GuardedClosure.Flow (Kernel.GTruth K) c
    ; mono      = λ {g} le → GC.GuardedClosure.mono (Kernel.GTruth K) le
    ; infl-sat  = GC.GuardedClosure.infl (Kernel.GTruth K)
    ; idemp-sat = GC.GuardedClosure.idemp-lax (Kernel.GTruth K)
    ; Th*       = GC.GuardedClosure.Th* (Kernel.GTruth K)
    ; Th*-fixed = GC.GuardedClosure.Th*-fixed (Kernel.GTruth K)
    }

asLogicKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → LogicKernel Sig Q
asLogicKernel K =
  record
    { shape       = Kernel.shape K
    ; G           = GTier-of-Kernel K
    ; guard-decode = Kernel.guard-decode K
    ; decode-γ*    = Kernel.decode-γ* K
    }

