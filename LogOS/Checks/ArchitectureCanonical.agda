{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ArchitectureCanonical where

-- Guardrail: ensure the canonical architecture / implementation / façade story typechecks.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
import LogOS.API.Kernel as KernelAPI
import LogOS.LT.LOG.Implementation2Cat.Definitional as IDef

module A = KernelAPI.Architecture
module I = KernelAPI.Implementation
module F = KernelAPI.Facade

K : A.Kernel lzero lzero lzero
K = A.BoundaryKernel UnitPreorder₀

_ : I.toFacadeHom (I.fromFacadeHom (F.idKernelHom K)) ≡ F.idKernelHom K
_ = IDef.to-fromKernelHom _

_ : I.LOGArchitectureImplementation {lzero} {lzero} {lzero}
    ≡ I.LOGᴳʳ {lzero} {lzero} {lzero}
_ = refl
