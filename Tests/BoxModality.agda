{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.BoxModality where

open import LogOS.Prelude using (Level)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

import LogOS.Kernel as K
import LogOS.Kernel.Graded as KG

module Ungraded {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (U : K.Kernel Sig Q) where
  stable-γ* : K.BoxStable U (K.Box U (K.Kernel.γ* U))
  stable-γ* = K.box-stable U (K.Kernel.γ* U)

  sat-closure = K.SatClosure U

  decode-closure-hom = K.decode-BoxClosureHom U

module Graded {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} (G : KG.GradedKernel Sig Q) where
  stable-γ* : KG.BoxStable G (KG.Box G (KG.GradedKernel.γ* G))
  stable-γ* = KG.box-stable G (KG.GradedKernel.γ* G)

  boxAt≤Box-γ* =
    KG.boxAt≤Box G (QAdapter.e Q) (KG.GradedKernel.γ* G)

  boxAt≤⊔s₁-γ* =
    KG.boxAt≤⊔s₁ G (QAdapter.e Q) (QAdapter.⊥s Q) (KG.GradedKernel.γ* G)

  boxAt≤⊔s₂-γ* =
    KG.boxAt≤⊔s₂ G (QAdapter.e Q) (QAdapter.⊥s Q) (KG.GradedKernel.γ* G)

  decode-closure-hom = KG.decode-BoxClosureHom G
