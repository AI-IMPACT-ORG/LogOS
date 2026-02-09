{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.WeilProbeImplication where

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)

-- Minimal “Weil probe” interface: a probe constructor plus the implication
-- W-pos (probe s) ⇒ OnLine s for nontrivial zeros.

record WeilProbeImplication {ℓS ℓW : Level}
                            (RS : RiemannSpectral)
                            (W  : Set ℓS)
                            (W-pos : W → Set ℓW)
                            : Set (lsuc (ℓS ⊔ ℓW)) where
  open RiemannSpectral RS
  field
    probe : Spectral → W
    probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s
