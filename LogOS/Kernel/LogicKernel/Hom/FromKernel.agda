{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Hom.FromKernel where

-- Bridge: a `KernelHom` induces a `LogicKernelHom` between the underlying
-- `LogicKernel`s (same shape, forget any model-specific flow preservation).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.Kernel
open import LogOS.Kernel.Hom
open import LogOS.Kernel.LogicKernel.FromKernel
open import LogOS.Kernel.LogicKernel.Hom

asLogicKernelHom
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
  → KernelHom K₁ K₂
  → LogicKernelHom (asLogicKernel K₁) (asLogicKernel K₂)
asLogicKernelHom h =
  record
    { con-hom    = KernelHom.con-hom h
    ; mapCode    = KernelHom.mapCode h
    ; map-encode = KernelHom.map-encode h
    ; map-decode = KernelHom.map-decode h
    }

