{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.BoundaryImplementation.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality-based implementation witness over architectural boundary transport.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; ≡→≈)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
import LogOS.LT.Coherence as Coherence
import LogOS.LT.BoundaryHom as Boundary
import LogOS.LT.BoundaryImplementation.Core as Core
import LogOS.LT.Strictification.Coherence as StrictCoherence

boundaryMap∂ = Boundary.BoundaryHom.map∂
boundaryMap∂-mono = Boundary.BoundaryHom.map∂-mono

record StrictBoundaryImplementation
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  (h∂ : Boundary.BoundaryHom K K')
  : Set (ℓCode ⊔ ℓCode' ⊔ StrictCoherence.StrictLevel ℓ ℓRel) where
  field
    mapCode : Code K → Code K'

    decode-mapCode
      : ∀ γ
      → StrictCoherence.StrictRel (bnd K')
          (decode K' (mapCode γ))
          (boundaryMap∂ h∂ (decode K γ))

implementCode
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
  → StrictBoundaryImplementation h∂
  → Code K → Code K'
implementCode = StrictBoundaryImplementation.mapCode

decode-implementsBoundary
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
    (impl : StrictBoundaryImplementation h∂)
  → ∀ γ
  → StrictCoherence.StrictRel (bnd K')
      (decode K' (implementCode impl γ))
      (boundaryMap∂ h∂ (decode K γ))
decode-implementsBoundary = StrictBoundaryImplementation.decode-mapCode

idBoundaryImplementation
  : ∀ {ℓ ℓRel ℓCode}
  → (K : Kernel ℓ ℓRel ℓCode)
  → StrictBoundaryImplementation (Boundary.idBoundaryHom K)
idBoundaryImplementation K =
  record
    { mapCode = λ γ → γ
    ; decode-mapCode = λ γ → StrictCoherence.strictRefl {CP = bnd K} (decode K γ)
    }

composeBoundaryImplementation
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
    {f∂ : Boundary.BoundaryHom K₁ K₂}
    {g∂ : Boundary.BoundaryHom K₂ K₃}
  → StrictBoundaryImplementation g∂
  → StrictBoundaryImplementation f∂
  → StrictBoundaryImplementation (Boundary._∘∂_ g∂ f∂)
composeBoundaryImplementation {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f∂ = f∂} {g∂ = g∂} g f =
  record
    { mapCode = λ γ → implementCode g (implementCode f γ)
    ; decode-mapCode = λ γ →
        StrictCoherence.strictTrans {CP = bnd K₃}
          (decode-implementsBoundary g (implementCode f γ))
          (StrictCoherence.strictMap
            {CP₁ = bnd K₂} {CP₂ = bnd K₃}
            {f = boundaryMap∂ g∂}
            (boundaryMap∂-mono g∂)
            (decode-implementsBoundary f γ))
    }

toApproxBoundaryImplementation
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
  → StrictBoundaryImplementation h∂
  → Core.BoundaryImplementation Coherence.approx h∂
toApproxBoundaryImplementation {K' = K'} impl =
  record
    { mapCode = implementCode impl
    ; decode-mapCode = λ γ → ≡→≈ {CP = bnd K'} (decode-implementsBoundary impl γ)
    }

toUnderBoundaryImplementation
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
  → StrictBoundaryImplementation h∂
  → Core.BoundaryImplementation Coherence.under h∂
toUnderBoundaryImplementation {K' = K'} impl =
  record
    { mapCode = implementCode impl
    ; decode-mapCode = λ γ → fst (≡→≈ {CP = bnd K'} (decode-implementsBoundary impl γ))
    }
