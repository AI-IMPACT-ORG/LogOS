{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Presentation.GeneratedImage where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Small generator-indexed local images inside a presentation.
--
-- This is the image-shaped companion to `GeneratedSubobject`:
-- - `GeneratedSubobject` filters existing generators,
-- - `GeneratedImage` reassigns each existing generator a target object and
--   rebuilds the resulting local image.
--
-- The canonical contract is refinement-first: image membership is recovered up
-- to a chosen congruence `_≈_`, while the equality-shaped strict record remains
-- available as explicit compatibility data.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

import LogOS.LT.Presentation.GeneratedSubobject.Core as Sub

record StrictGeneratedImages
  {ℓX ℓRel ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  (G : Sub.StrictLocalGenerators X (_∈_) ℓIx)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓIx)) where
  field
    generateImage
      : (x : X)
      → (Sub.StrictLocalGenerators.Ix G x → X)
      → X

    intoGeneratedImage
      : ∀ {x z}
      → (assign : Sub.StrictLocalGenerators.Ix G x → X)
      → (i : Sub.StrictLocalGenerators.Ix G x)
      → z ≡ assign i
      → z ∈ generateImage x assign

    outOfGeneratedImage
      : ∀ {x z}
      → (assign : Sub.StrictLocalGenerators.Ix G x → X)
      → z ∈ generateImage x assign
      → Σ (Sub.StrictLocalGenerators.Ix G x) (λ i → z ≡ assign i)

record GeneratedImages
  {ℓX ℓRel ℓEq ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  {_≈_ : X → X → Set ℓEq}
  (G : Sub.LocalGenerators X (_∈_) (_≈_) ℓIx)
  : Set (lsuc (ℓX ⊔ ℓRel ⊔ ℓEq ⊔ ℓIx)) where
  field
    strict : StrictGeneratedImages (Sub.LocalGenerators.strict G)

    intoGeneratedImage≈
      : ∀ {x z}
      → (assign : Sub.LocalGenerators.Ix G x → X)
      → (i : Sub.LocalGenerators.Ix G x)
      → z ≈ assign i
      → z ∈ StrictGeneratedImages.generateImage strict x assign

    outOfGeneratedImage≈
      : ∀ {x z}
      → (assign : Sub.LocalGenerators.Ix G x → X)
      → z ∈ StrictGeneratedImages.generateImage strict x assign
      → Σ (Sub.LocalGenerators.Ix G x) (λ i → z ≈ assign i)

  generateImage
    : (x : X)
    → (Sub.LocalGenerators.Ix G x → X)
    → X
  generateImage = StrictGeneratedImages.generateImage strict

  intoGeneratedImage
    : ∀ {x z}
    → (assign : Sub.LocalGenerators.Ix G x → X)
    → (i : Sub.LocalGenerators.Ix G x)
    → z ≡ assign i
    → z ∈ generateImage x assign
  intoGeneratedImage = StrictGeneratedImages.intoGeneratedImage strict

  outOfGeneratedImage
    : ∀ {x z}
    → (assign : Sub.LocalGenerators.Ix G x → X)
    → z ∈ generateImage x assign
    → Σ (Sub.LocalGenerators.Ix G x) (λ i → z ≡ assign i)
  outOfGeneratedImage = StrictGeneratedImages.outOfGeneratedImage strict

open GeneratedImages public using
  ( generateImage
  ; intoGeneratedImage
  ; intoGeneratedImage≈
  ; outOfGeneratedImage
  ; outOfGeneratedImage≈
  )

strictGeneratedImages
  : ∀
      {ℓX ℓRel ℓEq ℓIx : Level}
      {X : Set ℓX}
      {_∈_ : X → X → Set ℓRel}
      {_≈_ : X → X → Set ℓEq}
      (G : Sub.LocalGenerators X (_∈_) (_≈_) ℓIx)
      (I : StrictGeneratedImages (Sub.LocalGenerators.strict G))
  → (∀ {x y} → x ≈ y → x ≡ y)
  → (∀ {x y} → x ≡ y → x ≈ y)
  → GeneratedImages G
strictGeneratedImages G I extensionality ≡→≈ =
  record
    { strict = I
    ; intoGeneratedImage≈ =
        λ assign i z≈assign →
          StrictGeneratedImages.intoGeneratedImage I assign i (extensionality z≈assign)
    ; outOfGeneratedImage≈ =
        λ assign z∈ →
          let i , eq = StrictGeneratedImages.outOfGeneratedImage I assign z∈
          in
          i , ≡→≈ eq
    }

module For
  {ℓX ℓRel ℓEq ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  {_≈_ : X → X → Set ℓEq}
  (G : Sub.LocalGenerators X (_∈_) (_≈_) ℓIx)
  (I : GeneratedImages G)
  where

  module LG = Sub.LocalGenerators G
  module GI = GeneratedImages I

  generatedImage-spec
    : ∀ {x z}
    → (assign : LG.Ix x → X)
    → z ∈ GI.generateImage x assign
        ↔ Σ (LG.Ix x) (λ i → z ≈ assign i)
  generatedImage-spec assign =
    intro
      (GI.outOfGeneratedImage≈ assign)
      (λ { (i , eq) → GI.intoGeneratedImage≈ assign i eq })

module StrictFor
  {ℓX ℓRel ℓIx : Level}
  {X : Set ℓX}
  {_∈_ : X → X → Set ℓRel}
  (G : Sub.StrictLocalGenerators X (_∈_) ℓIx)
  (I : StrictGeneratedImages G)
  where

  module LG = Sub.StrictLocalGenerators G
  module GI = StrictGeneratedImages I

  generatedImage-spec
    : ∀ {x z}
    → (assign : LG.Ix x → X)
    → z ∈ GI.generateImage x assign
        ↔ Σ (LG.Ix x) (λ i → z ≡ assign i)
  generatedImage-spec assign =
    intro
      (GI.outOfGeneratedImage assign)
      (λ { (i , eq) → GI.intoGeneratedImage assign i eq })
