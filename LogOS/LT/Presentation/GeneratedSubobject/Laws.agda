{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.GeneratedSubobject.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
import LogOS.LT.Presentation.GeneratedSubobject.Core as Core

generatedSubobject-spec
  : ∀
      {ℓX ℓRel ℓEq ℓIx ℓCls : Level}
      {X : Set ℓX}
      {_∈_ : X → X → Set ℓRel}
      {_≈_ : X → X → Set ℓEq}
      (G : Core.LocalGenerators X _∈_ _≈_ ℓIx)
      (S : Core.GeneratedSubobjects G ℓCls)
      {x z}
    → (Q : Core.Ix G x → Set ℓCls)
    → z ∈ Core.generate S x Q
        ↔ Σ (Core.Ix G x) (λ i → Q i × (z ≈ Core.elemAt G x i))
generatedSubobject-spec G S = Core.For.generated-spec G S

classifiedGenerate-spec
  : ∀
      {ℓX ℓRel ℓEq ℓIx ℓCls ℓProp : Level}
      {X : Set ℓX}
      {_∈_ : X → X → Set ℓRel}
      {_≈_ : X → X → Set ℓEq}
      (G : Core.LocalGenerators X _∈_ _≈_ ℓIx)
      (S : Core.GeneratedSubobjects G ℓCls)
      {P : (x : X) → Core.Ix G x → Set ℓProp}
      (C : Core.SmallClassifier G ℓCls ℓProp P)
      {x z}
    → z ∈ Core.classifiedGenerate S C x
        ↔ Σ (Core.Ix G x) (λ i → P x i × (z ≈ Core.elemAt G x i))
classifiedGenerate-spec G S C = Core.WithClassifier.generated-classified-spec G S C
