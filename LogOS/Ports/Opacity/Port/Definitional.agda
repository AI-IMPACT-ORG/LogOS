{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.Port.Definitional where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View.Strictification using (_≃[_]_)
open import LogOS.Ports.Opacity.Port using (OpacityPort)

infix 4 _≃obs_

_≃obs_
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX}
    {O : ConPreorder ℓOCon ℓORel}
  → (P : OpacityPort X O)
  → X → X → Set ℓOCon
_≃obs_ P x y = x ≃[ OpacityPort.observe P ] y
