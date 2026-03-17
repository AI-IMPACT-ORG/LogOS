{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.ArchitecturalNormalFormStrictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality/strictification addendum to architectural normal form.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; ProductDisplayed
  ; DecoratedThin2Cat
  )
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.Hom.Core using (KernelHom)
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat
import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit2Cat
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode2Cat
import LogOS.LT.LOG.Discipline.StrictificationAsDisplayed as StrictificationAsDisplayed
import LogOS.LT.Theorems.ArchitecturalNormalForm as RefinementANF
import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.Ports.PortStack.ClassicalLimit as PortStackClassicalLimit
import LogOS.LT.Discipline.ArchitectureImplementationLaw.Strictification as LawStrictification

record ArchitecturalNormalFormStrictification
  (ℓ ℓRel ℓCode : Level)
  : Setω where
  field
    toFacadeHom-fromFacadeHom≡id
      : ∀ {K K' : Kernel ℓ ℓRel ℓCode}
      → (h : KernelHom K K')
      → Implementation2Cat.toFacadeHom (Implementation2Cat.fromFacadeHom h) ≡ h

    fromFacadeHom-toFacadeHom≡id
      : ∀ {K K' : Kernel ℓ ℓRel ℓCode}
      → (f : LogOS.LT.DisplayedThin2Cat.DecoratedHom
              (Implementation2Cat.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})
              (Implementation2Cat.embed K)
              (Implementation2Cat.embed K'))
      → Implementation2Cat.fromFacadeHom (Implementation2Cat.toFacadeHom f) ≡ f

    supportedStrictificationLayers
      : StrictificationAsDisplayed.SupportedStrictificationLayers ℓ ℓRel ℓCode

    strictifyDisplayed
      : ∀ {ℓDObj ℓDHom : Level}
          {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
        → Thin2Functor
            (DecoratedThin2Cat
              (ProductDisplayed (ClassicalLimit2Cat.ClassicalLimitDisplayed {ℓ} {ℓRel} {ℓCode}) D))
            (DecoratedThin2Cat
              (ProductDisplayed (StrictDecode2Cat.Displayed {ℓ} {ℓRel} {ℓCode}) D))

    strictifyStack
      : (S : PortStack.PortStack (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}))
      → Thin2Functor
          (PortStack.StackCat (PortStackClassicalLimit.withClassicalLimit {ℓ} {ℓRel} {ℓCode} S))
          (PortStack.StackCat (PortStackClassicalLimit.withStrictDecode {ℓ} {ℓRel} {ℓCode} S))

architecturalNormalFormStrictification
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ArchitecturalNormalFormStrictification ℓ ℓRel ℓCode
architecturalNormalFormStrictification {ℓ} {ℓRel} {ℓCode} =
  record
    { toFacadeHom-fromFacadeHom≡id = LawStrictification.toFacadeHom-fromFacadeHom≡id
    ; fromFacadeHom-toFacadeHom≡id = LawStrictification.fromFacadeHom-toFacadeHom≡id
    ; supportedStrictificationLayers = StrictificationAsDisplayed.supportedStrictificationLayers
    ; strictifyDisplayed = ClassicalLimit2Cat.strictifyDisplayed
    ; strictifyStack = PortStackClassicalLimit.strictifyStack
    }

refinementHalf
  : ∀ {ℓ ℓRel ℓCode : Level}
  → RefinementANF.ObservationPreservingArchitecturalNormalForm ℓ ℓRel ℓCode
refinementHalf = RefinementANF.architecturalNormalForm
