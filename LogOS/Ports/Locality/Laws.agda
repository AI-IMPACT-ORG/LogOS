{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Locality.Laws where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (_⊑[_]_)
open import LogOS.Ports.Locality.Core using (LocalityPort; localProbe)

⊑loc→probe⊑
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : I → ConPreorder ℓOCon ℓORel}
    (P : LocalityPort X I O)
    {x y : X}
  → LocalityPort._⊑loc_ P x y
  → ∀ i → x ⊑[ localProbe P i ] y
⊑loc→probe⊑ _ le i = le i
