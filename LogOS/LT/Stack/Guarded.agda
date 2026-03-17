{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack.Guarded where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude using (Level)
open import LogOS.LT.Coherence using (under)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom⊑)
import LogOS.LT.Stack.Core as Core

open Core public using
  ( Stack
  ; StackMapLike
  ; StackMap⊑
  ; toKernelHomLike
  ; fromKernelHomLike
  ; stackKernel
  )

toKernelHom⊑
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → StackMap⊑ S K'
  → KernelHom⊑ (stackKernel S) K'
toKernelHom⊑ = toKernelHomLike {m = under}

fromKernelHom⊑
  : ∀ {ℓB ℓRel ℓOp ℓCode ℓCode' : Level}
    {S : Stack {ℓB} {ℓRel} {ℓOp} {ℓCode}} {K' : Kernel ℓB ℓRel ℓCode'}
  → KernelHom⊑ (stackKernel S) K'
  → StackMap⊑ S K'
fromKernelHom⊑ = fromKernelHomLike {m = under}
