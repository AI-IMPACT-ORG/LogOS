{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.CTD where

-- A concrete, v1.1-native "Church-Turing-Deutsch principle" instance.
-- several paradigms admit a flow-preserving simulation into one universal kernel.
--
-- This module does not claim physics. It shows the transformer shape:
-- the CTD claim is a ledger that provides simulation adapters, and then the
-- effectivisation tooling loop is automatic. The same ledger now exposes
-- critical-budget cutpoints for measured agreement through the universality
-- agreement surface.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; refl⊑)
open import LogOS.LT.Flow using (GuardedClosure; idClosure)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Hom using (KernelHom)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.Ports.CriticalParameter using (CriticalCut)

import LogOS.Ports.Universality.Core as Core
open import LogOS.Ports.Universality.CTD.Ledger using (CTDLedger)
import LogOS.Apps.Universality.Stack as Stack

-- Any kernel morphism is flow-preserving for identity closures.
trivialKernelHomFlow
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K K' : Kernel ℓ ℓRel ℓCode}
    (h : KernelHom K K')
  → KernelHomFlow (idClosure (bnd K)) (idClosure (bnd K')) h
trivialKernelHomFlow {K' = K'} _ =
  record { preserves-Flow = λ _ → refl⊑ (bnd K') }

K : Stack.UniversalityAdapter → Kernel lzero lzero lzero
K = Stack.adapterKernel

GC : (s : Stack.UniversalityAdapter) → GuardedClosure (bnd (K s))
GC s = idClosure (bnd (K s))

simulate
  : (s : Stack.UniversalityAdapter)
  → Σ
      (KernelHom (K s) Core.universalKernel)
      (λ h → KernelHomFlow (GC s) (idClosure (bnd Core.universalKernel)) h)
simulate s = Stack.adapterKernelHom s , trivialKernelHomFlow (Stack.adapterKernelHom s)

simulateCriticalBudget
  : (s : Stack.UniversalityAdapter)
  → (γ : Stack.UniversalityAdapterCode s)
  → CriticalCut
      Core.universalBoundary
      (λ budget → Core.BudgetEnough (Stack.adapterCodeBoundary s γ) budget)
simulateCriticalBudget s γ =
  Stack.adapterCriticalBudget s γ

ctdLedger : CTDLedger {ℓ = lzero} {ℓRel = lzero} {ℓCode = lzero} {ℓSys = lzero}
ctdLedger =
  record
    { simulations = record
        { Sys = Stack.UniversalityAdapter
        ; K = K
        ; GC = GC
        ; U = Core.universalKernel
        ; GCᵁ = idClosure (bnd Core.universalKernel)
        ; simulate = simulate
        }
    }
