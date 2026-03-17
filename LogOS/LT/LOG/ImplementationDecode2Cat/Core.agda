{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.ImplementationDecode2Cat.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Decoded-only implementation view of the façade category `LOG`.
--
-- Reading:
-- - architecture: decoded refinement may be compared purely through boundary maps
-- - implementation: chosen code witnesses stay explicit rather than collapsed
-- - façade: `KernelHom` packages architecture and implementation together

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom; _⇒∂_; toKernelHomLikeR; boundaryPart)

open import LogOS.LT.LOG.BoundaryDecode2Cat using (_⇒ᵈ_)
open import LogOS.LT.LOG.Boundary2Cat using (BoundaryHomL)

private
  boundaryL
    : ∀ {ℓ ℓRel ℓCode : Level}
      {K : Kernel ℓ ℓRel ℓCode}
      {K' : Kernel ℓ ℓRel ℓCode}
    → KernelHom K K'
    → BoundaryHomL K K'
  boundaryL {ℓCode = ℓCode} h =
    lift {ℓ = ℓCode} (boundaryPart (toKernelHomLikeR h))

⇒ᵈ≡⇒∂
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
    {f g : KernelHom K K'}
  → _⇒ᵈ_ (boundaryL f) (boundaryL g) ≡ (f ⇒∂ g)
⇒ᵈ≡⇒∂ = refl

⇒↔⇒ᵈ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
    {f g : KernelHom K K'}
  → (f ⇒∂ g → _⇒ᵈ_ (boundaryL f) (boundaryL g))
    ×
    (_⇒ᵈ_ (boundaryL f) (boundaryL g) → f ⇒∂ g)
⇒↔⇒ᵈ = (λ fg → fg) , (λ fg → fg)
