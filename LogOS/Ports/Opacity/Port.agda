{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.Port where

-- Opacity as a port: an explicit observation boundary (a view).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.View using (View; PullbackPreorder; _⊑[_]_; _≈[_]_)
open import LogOS.LT.Kernel using (Kernel; kernelFromView)
open import LogOS.LT.Contracts using (Contract; mkContract)
open import LogOS.Ports.IO using (IOPort; uniformIOPort)

record OpacityPort {ℓX ℓOCon ℓORel : Level} (X : Set ℓX) (O : ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓOCon ⊔ ℓORel)) where
  field
    observe : View X O

  infix 4 _⊑obs_ _≈obs_

  _⊑obs_ : X → X → Set ℓORel
  x ⊑obs y = x ⊑[ observe ] y

  _≈obs_ : X → X → Set ℓORel
  x ≈obs y = x ≈[ observe ] y

toView
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX} {O : ConPreorder ℓOCon ℓORel}
  → OpacityPort X O → View X O
toView P = OpacityPort.observe P

fromView
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX} {O : ConPreorder ℓOCon ℓORel}
  → View X O → OpacityPort X O
fromView V = record { observe = V }

opacityKernel
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX} {O : ConPreorder ℓOCon ℓORel}
  → OpacityPort X O
  → Kernel ℓOCon ℓORel ℓX
opacityKernel P =
  kernelFromView (OpacityPort.observe P)

OpacityPreorder
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX} {O : ConPreorder ℓOCon ℓORel}
  → OpacityPort X O → ConPreorder ℓX ℓORel
OpacityPreorder P = PullbackPreorder (OpacityPort.observe P)

opacityContract
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX} {O : ConPreorder ℓOCon ℓORel}
  → OpacityPort X O
  → Con O
  → Contract {ℓ = ℓOCon} {ℓRel = ℓORel} {ℓCode = ℓX}
opacityContract P c = mkContract (opacityKernel P) c

opacityIOPort
  : ∀ {ℓX ℓOCon ℓORel}
    {X : Set ℓX} {O : ConPreorder ℓOCon ℓORel}
  → OpacityPort X O
  → IOPort {ℓI = lzero} {ℓA = lzero} X (⊤ {ℓ = lzero}) O
opacityIOPort P = uniformIOPort (λ _ → ⊤ {ℓ = lzero}) (OpacityPort.observe P)
