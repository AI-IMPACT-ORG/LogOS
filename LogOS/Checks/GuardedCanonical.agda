{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.GuardedCanonical where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.View using (View)

import LogOS.API.Kernel as KernelAPI
import LogOS.API.Guarded as GuardedAPI

K : KernelAPI.Kernel lzero lzero lzero
K = KernelAPI.BoundaryKernel UnitPreorder₀

_ : GuardedAPI.LOGGuarded {lzero} {lzero} {lzero}
    ≡ GuardedAPI.LOG⊑ {lzero} {lzero} {lzero}
_ = refl

_ : GuardedAPI.LOGArchitectureImplementationUnder {lzero} {lzero} {lzero}
    ≡ GuardedAPI.LOGᴳʳ⊑ {lzero} {lzero} {lzero}
_ = refl

_ : GuardedAPI.LOGArchitectureImplementationContractUnder {lzero} {lzero} {lzero}
    ≡ GuardedAPI.LOGᴳʳ∂⊑ {lzero} {lzero} {lzero}
_ = refl

_ : GuardedAPI.LOGArchitectureImplementationFlowUnder {lzero} {lzero} {lzero}
    ≡ GuardedAPI.LOGᴳʳᶠ⊑ {lzero} {lzero} {lzero}
_ = refl

UnitStack : GuardedAPI.Stack {lzero} {lzero} {lzero} {lzero}
UnitStack =
  record
    { bnd = UnitPreorder₀
    ; Op = ⊤
    ; Code = λ _ → ⊤
    ; op = λ _ → record { μ = λ _ → tt }
    }

guardedId
  : GuardedAPI.KernelHom⊑ (GuardedAPI.stackKernel UnitStack) (GuardedAPI.stackKernel UnitStack)
guardedId = GuardedAPI.approx→under (KernelAPI.idKernelHom (GuardedAPI.stackKernel UnitStack))

_ : GuardedAPI.toKernelHom⊑ (GuardedAPI.fromKernelHom⊑ guardedId) ≡ guardedId
_ = refl
