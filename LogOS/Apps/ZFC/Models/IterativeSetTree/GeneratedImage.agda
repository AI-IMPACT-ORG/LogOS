{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.GeneratedImage where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.LT.Presentation.GeneratedImage as Gen

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST
import LogOS.Apps.ZFC.Models.IterativeSetTree.GeneratedSubtree as Subtree

-- Generated images of iterative trees along assignments on the existing child
-- indices. This stays at the raw presentation level: no quotient, no collapse.
--
-- The exported LT data here is intentionally strict/equality-shaped. ZFC-side
-- refinement-first instantiations are obtained later by applying the canonical
-- LT adapters under explicit extensional-collapse assumptions.

imageOf
  : ∀ {ℓ}
  → (x : IST.V {ℓ})
  → (IST.Idx x → IST.V {ℓ})
  → IST.V {ℓ}
imageOf (IST.sup I _) assign = IST.sup I assign

imageOf-memberIn
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (assign : IST.Idx x → IST.V {ℓ})
  → (i : IST.Idx x)
  → z ≡ assign i
  → z IST.∈ᵛ imageOf x assign
imageOf-memberIn {x = IST.sup _ _} assign i eq = i , eq

imageOf-memberOut
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (assign : IST.Idx x → IST.V {ℓ})
  → z IST.∈ᵛ imageOf x assign
  → Σ (IST.Idx x) (λ i → z ≡ assign i)
imageOf-memberOut {x = IST.sup _ _} assign (i , eq) = i , eq

strictGeneratedImagesᵛ
  : ∀ {ℓ}
  → Gen.StrictGeneratedImages (Subtree.strictLocalGeneratorsᵛ {ℓ})
strictGeneratedImagesᵛ =
  record
    { generateImage = imageOf
    ; intoGeneratedImage = imageOf-memberIn
    ; outOfGeneratedImage = imageOf-memberOut
    }

module Impl {ℓ : Level} = Gen.StrictFor (Subtree.strictLocalGeneratorsᵛ {ℓ}) (strictGeneratedImagesᵛ {ℓ})

imageᵛ
  : ∀ {ℓ}
  → (x : IST.V {ℓ})
  → (IST.Idx x → IST.V {ℓ})
  → IST.V {ℓ}
imageᵛ {ℓ} = Gen.StrictGeneratedImages.generateImage (strictGeneratedImagesᵛ {ℓ})

image-memberIn
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (assign : IST.Idx x → IST.V {ℓ})
  → (i : IST.Idx x)
  → z ≡ assign i
  → z IST.∈ᵛ imageᵛ x assign
image-memberIn {ℓ} = Gen.StrictGeneratedImages.intoGeneratedImage (strictGeneratedImagesᵛ {ℓ})

image-memberOut
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (assign : IST.Idx x → IST.V {ℓ})
  → z IST.∈ᵛ imageᵛ x assign
  → Σ (IST.Idx x) (λ i → z ≡ assign i)
image-memberOut {ℓ} = Gen.StrictGeneratedImages.outOfGeneratedImage (strictGeneratedImagesᵛ {ℓ})

image-spec
  : ∀ {ℓ} {x z : IST.V {ℓ}}
  → (assign : IST.Idx x → IST.V {ℓ})
  → z IST.∈ᵛ imageᵛ x assign
      ↔ Σ (IST.Idx x) (λ i → z ≡ assign i)
image-spec = Impl.generatedImage-spec
