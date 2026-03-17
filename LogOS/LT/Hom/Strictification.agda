{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Hom.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality-based kernel morphism lane.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; MonoMap; ≡→≈)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
import LogOS.LT.BoundaryHom as Boundary
import LogOS.LT.BoundaryImplementation.Strictification as Implementation
import LogOS.LT.Hom.Core as Core
import LogOS.LT.Hom.Coercions as RefinementCoercions

boundaryMap∂ = Boundary.BoundaryHom.map∂
boundaryMap∂-mono = Boundary.BoundaryHom.map∂-mono

BoundaryImplementation = Implementation.StrictBoundaryImplementation
implementCode = Implementation.implementCode
decode-implementsBoundary = Implementation.decode-implementsBoundary
idBoundaryImplementation = Implementation.idBoundaryImplementation
composeBoundaryImplementation = Implementation.composeBoundaryImplementation

record KernelHom≡R
  {ℓ ℓRel ℓCode ℓCode' : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (K' : Kernel ℓ ℓRel ℓCode')
  : Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓCode' ⊔ ℓ) where
  constructor mkKernelHom≡R
  field
    boundary : Boundary.BoundaryHom K K'
    compat : BoundaryImplementation boundary

KernelHom≡
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
  → Kernel ℓ ℓRel ℓCode
  → Kernel ℓ ℓRel ℓCode'
  → Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓCode' ⊔ ℓ)
KernelHom≡ K K' = KernelHom≡R K K'

StrictKernelHom
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
  → Kernel ℓ ℓRel ℓCode
  → Kernel ℓ ℓRel ℓCode'
  → Set _
StrictKernelHom = KernelHom≡

boundaryPart
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom≡R K K'
  → Boundary.BoundaryHom K K'
boundaryPart = KernelHom≡R.boundary

implementationPart
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom≡R K K')
  → BoundaryImplementation (boundaryPart h)
implementationPart = KernelHom≡R.compat

mkKernelHom≡Parts
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h∂ : Boundary.BoundaryHom K K')
  → BoundaryImplementation h∂
  → KernelHom≡R K K'
mkKernelHom≡Parts = mkKernelHom≡R

map∂
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom≡ K K'
  → Con (bnd K) → Con (bnd K')
map∂ h = boundaryMap∂ (boundaryPart h)

map∂-mono
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom≡ K K')
  → MonoMap (bnd K) (bnd K') (map∂ h)
map∂-mono h = boundaryMap∂-mono (boundaryPart h)

mapCode
  : ∀ {ℓ ℓRel ℓCode ℓCode'}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom≡ K K'
  → Code K → Code K'
mapCode h = implementCode (implementationPart h)

decode-mapCode≡
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : StrictKernelHom K K')
  → ∀ γ
  → decode K' (mapCode h γ) ≡ map∂ h (decode K γ)
decode-mapCode≡ h = decode-implementsBoundary (implementationPart h)

strict→approx
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom≡ K K'
  → Core.KernelHom K K'
strict→approx {K' = K'} h =
  Core.mkKernelHomParts
    (boundaryPart h)
    (record
      { mapCode = mapCode h
      ; decode-mapCode = λ γ → ≡→≈ {CP = bnd K'} (decode-mapCode≡ h γ)
      })

strict→under
  : ∀ {ℓ ℓRel ℓCode ℓCode' : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → KernelHom≡ K K'
  → Core.KernelHom⊑ K K'
strict→under h = RefinementCoercions.approx→under (strict→approx h)

idKernelHom≡
  : ∀ {ℓ ℓRel ℓCode}
  → (K : Kernel ℓ ℓRel ℓCode)
  → KernelHom≡ K K
idKernelHom≡ K =
  mkKernelHom≡Parts
    (Boundary.idBoundaryHom K)
    (idBoundaryImplementation K)

infixr 40 _∘≡_
_∘≡_
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ ℓCode₃ : Level}
    {K₁ : Kernel ℓ ℓRel ℓCode₁}
    {K₂ : Kernel ℓ ℓRel ℓCode₂}
    {K₃ : Kernel ℓ ℓRel ℓCode₃}
  → KernelHom≡ K₂ K₃
  → KernelHom≡ K₁ K₂
  → KernelHom≡ K₁ K₃
_∘≡_ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g f =
  mkKernelHom≡Parts
    (Boundary._∘∂_ (boundaryPart g) (boundaryPart f))
    (composeBoundaryImplementation {K₁ = K₁} {K₂ = K₂} {K₃ = K₃}
      {f∂ = boundaryPart f} {g∂ = boundaryPart g}
      (implementationPart g)
      (implementationPart f))

decode-mapCode-cong
  : ∀ {ℓ ℓRel ℓCode ℓCode' ℓX : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode'}
  → (h : KernelHom≡ K K')
    {X : Set ℓX}
  → (obs : Con (bnd K') → X)
  → ∀ γ
  → obs (decode K' (mapCode h γ)) ≡ obs (map∂ h (decode K γ))
decode-mapCode-cong h obs γ =
  cong obs (decode-mapCode≡ h γ)
