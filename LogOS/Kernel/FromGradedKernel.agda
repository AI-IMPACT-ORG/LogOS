{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.FromGradedKernel where

-- Instance bridge: any `GradedKernel` yields a `Kernel` by taking
-- `Step = Scale` and using the graded saturation step `sat`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded
open import LogOS.Kernel
open import LogOS.Kernel.GuardedTier as GT
import LogOS.Kernel.Graded.Hom as GradedHom
import LogOS.Kernel.Hom as KernelHom

GTier-of-GradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → GTier Q (BulkBoundary.bnd (GradedKernel.BB K))
GTier-of-GradedKernel K =
  GT.fromGradedClosure (GradedKernel.GTruth K) (GradedKernel.step-grade K)

asKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : GradedKernel Sig Q)
  → Kernel Sig Q
asKernel K =
  record
    { shape       = GradedKernel.shape K
    ; shapeLaws   = GradedKernel.shapeLaws K
    ; G           = GTier-of-GradedKernel K
    ; guard-decode = GradedKernel.guard-decode K
    ; decode-γ*    = GradedKernel.decode-γ* K
    }

-- Morphism bridge: forget graded flow structure and view a `GradedKernelHom`
-- as a plain `KernelHom` between the underlying `Kernel`s.

asKernelHom
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K₁ K₂ : GradedKernel Sig Q}
  → GradedHom.GradedKernelHom K₁ K₂
  → KernelHom.KernelHom (asKernel K₁) (asKernel K₂)
asKernelHom h =
  record
    { con-hom    = GradedHom.GradedKernelHom.con-hom h
    ; mapCode    = GradedHom.GradedKernelHom.mapCode h
    ; map-encode = GradedHom.GradedKernelHom.map-encode h
    ; map-decode = GradedHom.GradedKernelHom.map-decode h
    }
