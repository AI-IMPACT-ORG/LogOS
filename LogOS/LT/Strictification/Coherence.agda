{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Strictification.Coherence where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Explicit strict/equality coherence lane.
--
-- This module is the only LT coherence surface whose primary law is Agda
-- propositional equality. Default LT surfaces import `LogOS.LT.Coherence`
-- instead.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder as Con using
  ( ConPreorder
  ; Con
  ; MonoMap
  )

StrictLevel : Level → Level → Level
StrictLevel ℓCon _ = ℓCon

StrictRel
  : ∀ {ℓCon ℓRel}
  → (CP : ConPreorder ℓCon ℓRel)
  → Con CP
  → Con CP
  → Set (StrictLevel ℓCon ℓRel)
StrictRel _ x y = x ≡ y

strictRefl
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (x : Con CP)
  → StrictRel CP x x
strictRefl _ = refl

strictTrans
  : ∀ {ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel} {x y z : Con CP}
  → StrictRel CP x y
  → StrictRel CP y z
  → StrictRel CP x z
strictTrans = trans

strictMap
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {CP₁ : ConPreorder ℓCon₁ ℓRel₁}
    {CP₂ : ConPreorder ℓCon₂ ℓRel₂}
    {f : Con CP₁ → Con CP₂}
    {x y : Con CP₁}
  → MonoMap CP₁ CP₂ f
  → StrictRel CP₁ x y
  → StrictRel CP₂ (f x) (f y)
strictMap {f = f} _ eq = cong f eq
