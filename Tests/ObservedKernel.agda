{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.ObservedKernel where

open import LogOS.Prelude

open import LogOS.UniversalIR.ObservedKernel
open import LogOS.UniversalIR.Core using (UCode; UM; UL; UE; UQ; UQC; stepU)
import LogOS.Computation.SchemeCategory as Cat

module Code = ObsKit CodeObsKit
module Lambda = ObsKit LambdaObsKit

-- Code observation is the identity on the universal carrier.
code-observe-id : ∀ u → Code.observeU u ≡ u
code-observe-id _ = refl

-- Lambda observation is a step homomorphism (by definitional computation).
lambda-observe-step
  : ∀ u → Lambda.observeU (stepU u) ≡ Lambda.obsStep (Lambda.observeU u)
lambda-observe-step (UL _)  = refl
lambda-observe-step (UM _)  = refl
lambda-observe-step (UE _)  = refl
lambda-observe-step (UQ _)  = refl
lambda-observe-step (UQC _) = refl

-- KernelUniversalProcess bridge produces identity boundary decoding.
module CodeProc = ForObsKit CodeObsKit
open CodeProc.Process

code-boundary-decode-id : ∀ c → Cat.Process.decode BoundaryProcess c ≡ c
code-boundary-decode-id _ = refl
