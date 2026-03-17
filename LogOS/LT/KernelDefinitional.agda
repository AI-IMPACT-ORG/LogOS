{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.KernelDefinitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Definitional/bookkeeping equalities for kernels.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (View; PullbackPreorder)
open import LogOS.LT.View.Roles using (forget)
open import LogOS.LT.Kernel using (Kernel; kernelFromView; decodeView; CodePreorder)

decodeView-kernelFromView
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    (V : View X O)
  → forget (decodeView (kernelFromView V)) ≡ V
decodeView-kernelFromView _ = refl

codePreorder-kernelFromView
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
    (V : View X O)
  → CodePreorder (kernelFromView V) ≡ PullbackPreorder V
codePreorder-kernelFromView _ = refl
