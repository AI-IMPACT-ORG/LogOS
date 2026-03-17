{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Conventions.BoundaryRefinementForgetsImplementation where

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.View using (_⊑[_]_)
open import LogOS.LT.View.Roles using (forget)
open import LogOS.LT.Hom.Core using (KernelHom; transportView; _⇒∂_)

boundary-refinement-is-boundary-onlyDef
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {f g : KernelHom K K'}
  → (f ⇒∂ g) ≡ (f ⊑[ forget (transportView {K = K} {K' = K'}) ] g)
boundary-refinement-is-boundary-onlyDef = refl
