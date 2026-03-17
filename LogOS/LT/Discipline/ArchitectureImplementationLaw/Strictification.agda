{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Discipline.ArchitectureImplementationLaw.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality/strictification witnesses for the architecture / implementation /
-- façade split.

open import LogOS.Prelude using (Level; _≡_)
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.Hom.Core using (KernelHom)
open import LogOS.LT.DisplayedThin2Cat using (DecoratedHom)
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat
import LogOS.LT.LOG.Implementation2Cat.Definitional as Implementation2CatDefinitional

toFacadeHom-fromFacadeHom≡id
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (h : KernelHom K K')
  → Implementation2Cat.toFacadeHom (Implementation2Cat.fromFacadeHom h) ≡ h
toFacadeHom-fromFacadeHom≡id = Implementation2CatDefinitional.to-fromKernelHom

fromFacadeHom-toFacadeHom≡id
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (f : DecoratedHom
          (Implementation2Cat.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})
          (Implementation2Cat.embed K)
          (Implementation2Cat.embed K'))
  → Implementation2Cat.fromFacadeHom (Implementation2Cat.toFacadeHom f) ≡ f
fromFacadeHom-toFacadeHom≡id = Implementation2CatDefinitional.from-toKernelHom
