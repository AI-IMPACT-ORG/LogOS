{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.Hom.FromGradedKernel where

-- Bridge: a `GradedKernelHom` induces a `LogicKernelHom` between the underlying
-- `LogicKernel`s (same shape, forget any graded-flow preservation structure).

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.Kernel.Graded
open import LogOS.Kernel.Graded.Hom
open import LogOS.Kernel.LogicKernel.FromGradedKernel
open import LogOS.Kernel.LogicKernel.Hom

asLogicKernelHom
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
  → GradedKernelHom K₁ K₂
  → LogicKernelHom (asLogicKernel K₁) (asLogicKernel K₂)
asLogicKernelHom h =
  record
    { con-hom    = GradedKernelHom.con-hom h
    ; mapCode    = GradedKernelHom.mapCode h
    ; map-encode = GradedKernelHom.map-encode h
    ; map-decode = GradedKernelHom.map-decode h
    }

