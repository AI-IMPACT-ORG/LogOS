{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Hom.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-facing laws for kernel morphisms.
--
-- The core representation stays in `LogOS.LT.Hom.Core`; this module names the
-- coherence-indexed law surface explicitly.

open import LogOS.Prelude
open import LogOS.LT.Coherence using (CohMode; CohRel)
open import LogOS.LT.Kernel using (Kernel; Code; bnd; decode)
open import LogOS.LT.Hom.Core using
  ( KernelHomLike
  ; map∂
  ; mapCode
  ; decode-mapCode
  ; idKernelHomLike
  )
import LogOS.LT.Hom.Core as Hom

KernelHomDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (h : KernelHomLike m K K')
  → Set _
KernelHomDecodeLaw {m = m} {K = K} {K' = K'} h =
  ∀ γ
  → CohRel m (bnd K')
      (decode K' (mapCode h γ))
      (map∂ h (decode K γ))

kernelHomDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    (h : KernelHomLike m K K')
  → KernelHomDecodeLaw h
kernelHomDecodeLaw h = decode-mapCode h

idKernelHomDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
  → KernelHomDecodeLaw (idKernelHomLike {m = m} K)
idKernelHomDecodeLaw {m = m} K =
  kernelHomDecodeLaw (idKernelHomLike {m = m} K)

composeKernelHomDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
    (g : KernelHomLike m K₂ K₃)
    (f : KernelHomLike m K₁ K₂)
  → KernelHomDecodeLaw (Hom._∘Like_ {m = m} g f)
composeKernelHomDecodeLaw g f =
  kernelHomDecodeLaw (Hom._∘Like_ g f)
