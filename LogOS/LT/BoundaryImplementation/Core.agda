{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.BoundaryImplementation.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Primitive refinement-tier witness over architectural boundary transport.
--
-- Reading:
-- - architecture: `BoundaryHom`
-- - implementation: a chosen code-level witness realises that transport
-- - law: further displayed doctrine layers may be stacked afterwards
--
-- Equality-based decode coherence is intentionally excluded here. That lane
-- lives in `LogOS.LT.BoundaryImplementation.Strictification`.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
import LogOS.LT.Coherence as Coherence
import LogOS.LT.BoundaryHom as Boundary

boundaryMap∂ = Boundary.BoundaryHom.map∂
boundaryMap∂-mono = Boundary.BoundaryHom.map∂-mono

record BoundaryImplementation
  (m : Coherence.CohMode)
  {ℓ ℓRel ℓCode ℓCode' : Level}
  {K : Kernel ℓ ℓRel ℓCode}
  {K' : Kernel ℓ ℓRel ℓCode'}
  (h∂ : Boundary.BoundaryHom K K')
  : Set (ℓCode ⊔ ℓCode' ⊔ Coherence.CohLevel m ℓ ℓRel) where
  field
    mapCode : Code K → Code K'

    decode-mapCode
      : ∀ γ
      → Coherence.CohRel m (bnd K')
          (decode K' (mapCode γ))
          (boundaryMap∂ h∂ (decode K γ))

implementCode
  : ∀ {m ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
  → BoundaryImplementation m h∂
  → Code K → Code K'
implementCode = BoundaryImplementation.mapCode

decode-implementsBoundary
  : ∀ {m ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
    (impl : BoundaryImplementation m h∂)
  → ∀ γ
  → Coherence.CohRel m (bnd K')
      (decode K' (implementCode impl γ))
      (boundaryMap∂ h∂ (decode K γ))
decode-implementsBoundary = BoundaryImplementation.decode-mapCode

idBoundaryImplementation
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode}
  → (K : Kernel ℓ ℓRel ℓCode)
  → BoundaryImplementation m (Boundary.idBoundaryHom K)
idBoundaryImplementation {m = m} K =
  record
    { mapCode = λ γ → γ
    ; decode-mapCode = λ γ → Coherence.cohRefl {m = m} (decode K γ)
    }

composeBoundaryImplementation
  : ∀ {m : Coherence.CohMode} {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
    {f∂ : Boundary.BoundaryHom K₁ K₂}
    {g∂ : Boundary.BoundaryHom K₂ K₃}
  → BoundaryImplementation m g∂
  → BoundaryImplementation m f∂
  → BoundaryImplementation m (Boundary._∘∂_ g∂ f∂)
composeBoundaryImplementation {m = m} {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {f∂ = f∂} {g∂ = g∂} g f =
  record
    { mapCode = λ γ → implementCode g (implementCode f γ)
    ; decode-mapCode = λ γ →
        Coherence.cohTrans
          {m = m} {CP = bnd K₃}
          (decode-implementsBoundary g (implementCode f γ))
          (Coherence.cohMap
            {m = m} {CP₁ = bnd K₂} {CP₂ = bnd K₃}
            {f = boundaryMap∂ g∂}
            (boundaryMap∂-mono g∂)
            (decode-implementsBoundary f γ))
    }
