{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Guarded where

-- Curated guarded-refinement surface.

open import LogOS.LT.Coherence public using (under)
open import LogOS.LT.Hom.Core public using (KernelHom⊑)
open import LogOS.LT.Hom.Coercions public using (approx→under)
open import LogOS.LT.LOG.GuardedKernel2Cat public using
  ( _⇒⊑_
  ; whiskerL⊑
  ; whiskerR⊑
  ; KernelHomPreorder⊑
  ; LOG⊑
  ; LOGGuarded
  )
open import LogOS.LT.LOG.GuardedImplementation2Cat public using
  ( ImplementationDisplayedUnder
  ; LOGᴳʳ⊑
  ; LOGArchitectureImplementationUnder
  ; toLOGUnder
  )
open import LogOS.LT.LOG.GuardedImplementationContract2Cat public using
  ( ImplementationContractStackUnder
  ; LOGᴳʳ∂⊑
  ; LOGArchitectureImplementationContractUnder
  )
open import LogOS.LT.LOG.GuardedImplementationFlow2Cat public using
  ( ImplementationFlowStackUnder
  ; LOGᴳʳᶠ⊑
  ; LOGArchitectureImplementationFlowUnder
  )
open import LogOS.LT.Stack.Guarded public using
  ( Stack
  ; StackMap⊑
  ; stackKernel
  ; toKernelHom⊑
  ; fromKernelHom⊑
  )
