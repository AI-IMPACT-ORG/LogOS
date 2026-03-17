{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.BoundaryHom where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Primitive boundary transport for kernels.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( Con
  ; MonoMap
  ; idMonoMap
  ; compMonoMap
  )
open import LogOS.LT.Kernel using (Kernel; bnd)

record BoundaryHom
  {ℓ ℓRel ℓCode ℓCode' : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (K' : Kernel ℓ ℓRel ℓCode')
  : Set (lsuc (ℓ ⊔ ℓRel)) where
  field
    map∂ : Con (bnd K) → Con (bnd K')
    map∂-mono : MonoMap (bnd K) (bnd K') map∂

idBoundaryHom : ∀ {ℓ ℓRel ℓCode} (K : Kernel ℓ ℓRel ℓCode) → BoundaryHom K K
idBoundaryHom K =
  record
    { map∂ = λ c → c
    ; map∂-mono = idMonoMap {CP = bnd K}
    }

infixr 40 _∘∂_
_∘∂_
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → BoundaryHom K₂ K₃
  → BoundaryHom K₁ K₂
  → BoundaryHom K₁ K₃
_∘∂_ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g f =
  record
    { map∂ = λ c → BoundaryHom.map∂ g (BoundaryHom.map∂ f c)
    ; map∂-mono =
        compMonoMap
          {CP₁ = bnd K₁}
          {CP₂ = bnd K₂}
          {CP₃ = bnd K₃}
          {f = BoundaryHom.map∂ f}
          {g = BoundaryHom.map∂ g}
          (BoundaryHom.map∂-mono f)
          (BoundaryHom.map∂-mono g)
    }
