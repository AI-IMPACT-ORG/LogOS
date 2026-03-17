{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.IO.Definitional where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View.Strictification using (_≃[_]_)
open import LogOS.Ports.IO using (IOPort)

infix 4 _≃io_

_≃io_
  : ∀ {ℓX ℓI ℓA ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → (P : IOPort {ℓA = ℓA} X I O)
  → X → X → Set (ℓI ⊔ ℓA ⊔ ℓOCon)
_≃io_ P x y = ∀ i → IOPort.admissible P i → x ≃[ IOPort.outputObs P i ] y
