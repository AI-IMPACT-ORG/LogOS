{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.BoundaryImplementation.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-facing laws for code-level boundary implementations.
--
-- Strict/equality-valued coherence remains quarantined in explicit
-- strictification or definitional lanes.

open import LogOS.Prelude
open import LogOS.LT.Coherence using (CohMode; CohRel)
open import LogOS.LT.Kernel using (Kernel; Code; bnd; decode)
open import LogOS.LT.BoundaryImplementation.Core using
  ( BoundaryImplementation
  ; boundaryMap∂
  ; implementCode
  ; decode-implementsBoundary
  ; idBoundaryImplementation
  ; composeBoundaryImplementation
  )
import LogOS.LT.BoundaryHom as Boundary

BoundaryImplementationDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
    (impl : BoundaryImplementation m h∂)
  → Set _
BoundaryImplementationDecodeLaw {m = m} {K = K} {K' = K'} {h∂ = h∂} impl =
  ∀ γ
  → CohRel m (bnd K')
      (decode K' (implementCode impl γ))
      (boundaryMap∂ h∂ (decode K γ))

boundaryImplementationDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
    {h∂ : Boundary.BoundaryHom K K'}
    (impl : BoundaryImplementation m h∂)
  → BoundaryImplementationDecodeLaw impl
boundaryImplementationDecodeLaw impl = decode-implementsBoundary impl

idBoundaryImplementationDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode : Level}
    (K : Kernel ℓ ℓRel ℓCode)
  → BoundaryImplementationDecodeLaw (idBoundaryImplementation {m = m} K)
idBoundaryImplementationDecodeLaw {m = m} K =
  boundaryImplementationDecodeLaw (idBoundaryImplementation {m = m} K)

composeBoundaryImplementationDecodeLaw
  : ∀ {m : CohMode} {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
    {f∂ : Boundary.BoundaryHom K₁ K₂}
    {g∂ : Boundary.BoundaryHom K₂ K₃}
    (g : BoundaryImplementation m g∂)
    (f : BoundaryImplementation m f∂)
  → BoundaryImplementationDecodeLaw
      (composeBoundaryImplementation
        {m = m}
        {K₁ = K₁}
        {K₂ = K₂}
        {K₃ = K₃}
        {f∂ = f∂}
        {g∂ = g∂}
        g
        f)
composeBoundaryImplementationDecodeLaw {m = m} g f =
  boundaryImplementationDecodeLaw
    (composeBoundaryImplementation
      {m = m}
      g
      f)
