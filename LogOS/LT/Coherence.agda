{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Coherence where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Primitive refinement-first coherence modes for kernel morphisms.
--
-- Equality is intentionally *not* ambient here. Strict coherence lives in the
-- explicit `LogOS.LT.Strictification.Coherence` lane.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder as Con using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; _≈_
  ; MonoMap
  ; monoMap-≈
  ; refl⊑
  ; ≈-refl
  )

data CohMode : Set where
  approx under : CohMode

CohLevel : CohMode → Level → Level → Level
CohLevel approx _ ℓRel = ℓRel
CohLevel under _ ℓRel = ℓRel

CohRel
  : ∀ {ℓCon ℓRel}
  → (m : CohMode)
  → (CP : ConPreorder ℓCon ℓRel)
  → Con CP
  → Con CP
  → Set (CohLevel m ℓCon ℓRel)
CohRel approx CP x y = _≈_ CP x y
CohRel under CP x y = _⊑_ CP x y

cohRefl
  : ∀ {m ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel}
  → (x : Con CP)
  → CohRel m CP x x
cohRefl {m = approx} {CP = CP} x = ≈-refl CP x
cohRefl {m = under} {CP = CP} x = refl⊑ CP {c = x}

cohTrans
  : ∀ {m ℓCon ℓRel} {CP : ConPreorder ℓCon ℓRel} {x y z : Con CP}
  → CohRel m CP x y
  → CohRel m CP y z
  → CohRel m CP x z
cohTrans {m = approx} {CP = CP} {x = x} xy yz =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning CP
  in
  R._≈⟨_⟩_ x xy yz
cohTrans {m = under} {CP = CP} {x = x} xy yz =
  let
    module R = LogOS.Prelude.RefinementKit.Reasoning CP
  in
  R._⊑⟨_⟩_ x xy yz

cohMap
  : ∀ {m ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {CP₁ : ConPreorder ℓCon₁ ℓRel₁}
    {CP₂ : ConPreorder ℓCon₂ ℓRel₂}
    {f : Con CP₁ → Con CP₂}
    {x y : Con CP₁}
  → MonoMap CP₁ CP₂ f
  → CohRel m CP₁ x y
  → CohRel m CP₂ (f x) (f y)
cohMap {m = approx} {CP₁ = CP₁} {CP₂ = CP₂} {f = f} {x = x} {y = y} mono eq =
  monoMap-≈ {CP₁ = CP₁} {CP₂ = CP₂} {f = f} mono x y eq
cohMap {m = under} mono le = mono le
