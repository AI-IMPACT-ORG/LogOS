{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.ArchitecturalNormalForm where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Observation-preserving architectural normal form.
--
-- This module packages the current LT-core theorem spine:
-- - observation forces the canonical pullback refinements,
-- - façade morphisms factor through boundary transport plus implementation,
-- - displayed totalisation inherits refinement from the base only,
-- - canonical LT layers are displayed/Σ-totalised by construction.
--
-- Equality-valued façade identities and strictification functors live in
-- `LogOS.LT.Theorems.ArchitecturalNormalFormStrictification`.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_)
open import LogOS.LT.View using (View; _⊑[_]_)
open import LogOS.LT.Kernel using (Kernel; Code)
open import LogOS.LT.Coherence using (approx)
open import LogOS.LT.Hom.Core using (KernelHom; KernelHomLike; KernelHomLikeR)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; ProductDisplayed
  ; TotalObj
  ; TotalHom
  ; TotalHomPreorder
  ; base
  ; baseHom
  ; DecoratedThin2Cat
  )

import LogOS.LT.Presentation as PresentationTheory
import LogOS.LT.Presentation.ObservationInitiality as ObservationInitialityTheory
import LogOS.LT.Discipline.ArchitectureImplementationLaw as ArchitectureImplementationLaw
import LogOS.LT.DisplayedThin2Cat.Totalisation as Totalisation
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat
import LogOS.LT.LOG.Discipline.PortsAsDisplayed.Definitional as PortsAsDisplayed

record ObservationPreservingArchitecturalNormalForm
  (ℓ ℓRel ℓCode : Level)
  : Setω where
  field
    presentation↔canonical
      : ∀ {ℓX ℓR ℓOCon ℓORel : Level}
          {X : Set ℓX}
          {O : ConPreorder ℓOCon ℓORel}
          {V : View X O}
          (P : PresentationTheory.Presentation {ℓR = ℓR} V)
        → PresentationTheory.CompletePresentation P
        → ∀ {x y}
        → (PresentationTheory.Presentation._≼_ P x y) ↔ (x ⊑[ V ] y)

    suiteForced
      : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
          {X : Set ℓX}
          {I : Set ℓI}
          {O : ConPreorder ℓOCon ℓORel}
          (S : ObservationInitialityTheory.ProbeSuite X I O)
          (≼ : X → X → Set ℓR)
        → (∀ {x y} → ≼ x y → ∀ i → x ⊑[ ObservationInitialityTheory.probe S i ] y)
        → ∀ {x y} → ≼ x y → ObservationInitialityTheory._⊑⟦_⟧_ x S y

    suiteForcedᵈ
      : ∀ {ℓX ℓI ℓOCon ℓORel ℓR}
          {X : Set ℓX}
          {I : Set ℓI}
          {O : I → ConPreorder ℓOCon ℓORel}
          (S : ObservationInitialityTheory.DependentProbeSuite X I O)
          (≼ : X → X → Set ℓR)
        → (∀ {x y} → ≼ x y → ∀ i → x ⊑[ ObservationInitialityTheory.probe S i ] y)
        → ∀ {x y} → ≼ x y → ObservationInitialityTheory._⊑⟦_⟧ᵈ_ x S y

    codeRefineForced
      : ∀ {ℓR}
          (K : Kernel ℓ ℓRel ℓCode)
          (≼ : Code K → Code K → Set ℓR)
        → (∀ {γ δ}
            → ≼ γ δ
            → _⊑_ (LogOS.LT.Kernel.bnd K)
                (LogOS.LT.Kernel.decode K γ)
                (LogOS.LT.Kernel.decode K δ))
        → ∀ {γ δ}
            → ≼ γ δ
            → _⊑_ (LogOS.LT.Kernel.CodePreorder K) γ δ

    morRefineForced∂
      : ∀ {ℓR} {ℓCode'}
          {K : Kernel ℓ ℓRel ℓCode}
          {K' : Kernel ℓ ℓRel ℓCode'}
        → (≼ : KernelHom K K' → KernelHom K K' → Set ℓR)
        → (∀ {f g}
            → ≼ f g
            → (∀ γ
                → _⊑_ (LogOS.LT.Kernel.bnd K')
                    (LogOS.LT.Hom.Core.transportObs {K = K} f γ)
                    (LogOS.LT.Hom.Core.transportObs {K = K} g γ)))
        → ∀ {f g} → ≼ f g → LogOS.LT.Hom.Core._⇒∂_ f g

    morRefineForced
      : ∀ {ℓR} {ℓCode'}
          {K : Kernel ℓ ℓRel ℓCode}
          {K' : Kernel ℓ ℓRel ℓCode'}
        → (≼ : KernelHom K K' → KernelHom K K' → Set ℓR)
        → (∀ {f g}
            → ≼ f g
            → (∀ γ
                → _⊑_ (LogOS.LT.Kernel.bnd K')
                    (LogOS.LT.Hom.Core.obs f γ)
                    (LogOS.LT.Hom.Core.obs g γ)))
        → ∀ {f g} → ≼ f g → LogOS.LT.Hom.Core._⇒_ f g

    kernelHomFactorises
      : ∀ {ℓCode'}
          (K : Kernel ℓ ℓRel ℓCode)
          (K' : Kernel ℓ ℓRel ℓCode')
      → KernelHomLike approx K K'
        ≡ KernelHomLikeR approx K K'

    implementationTotalisation
      : Implementation2Cat.LOGᴳʳ {ℓ} {ℓRel} {ℓCode}
        ≡
        DecoratedThin2Cat (Implementation2Cat.ImplementationDisplayed {ℓ} {ℓRel} {ℓCode})

    total⊑→base⊑
      : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
          {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
          (D : DisplayedThin2Cat C ℓDObj ℓDHom)
          {X Y : TotalObj D}
          {f g : TotalHom D X Y}
        → _⊑_ (TotalHomPreorder D X Y) f g
        → _⊑_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
            (baseHom {D = D} f)
            (baseHom {D = D} g)

    base⊑→total⊑
      : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
          {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
          (D : DisplayedThin2Cat C ℓDObj ℓDHom)
          {X Y : TotalObj D}
          {f g : TotalHom D X Y}
        → _⊑_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
            (baseHom {D = D} f)
            (baseHom {D = D} g)
        → _⊑_ (TotalHomPreorder D X Y) f g

    total≈→base≈
      : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
          {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
          (D : DisplayedThin2Cat C ℓDObj ℓDHom)
          {X Y : TotalObj D}
          {f g : TotalHom D X Y}
        → _≈_ (TotalHomPreorder D X Y) f g
        → _≈_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
            (baseHom {D = D} f)
            (baseHom {D = D} g)

    base≈→total≈
      : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
          {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
          (D : DisplayedThin2Cat C ℓDObj ℓDHom)
          {X Y : TotalObj D}
          {f g : TotalHom D X Y}
        → _≈_ (Thin2Cat.Hom C (base {D = D} X) (base {D = D} Y))
            (baseHom {D = D} f)
            (baseHom {D = D} g)
        → _≈_ (TotalHomPreorder D X Y) f g

    supportedArchitectureLayers
      : PortsAsDisplayed.SupportedArchitectureLayers ℓ ℓRel ℓCode

architecturalNormalForm
  : ∀ {ℓ ℓRel ℓCode : Level}
  → ObservationPreservingArchitecturalNormalForm ℓ ℓRel ℓCode
architecturalNormalForm {ℓ} {ℓRel} {ℓCode} =
  record
    { presentation↔canonical = PresentationTheory.presentation↔canonical
    ; suiteForced = ObservationInitialityTheory.SuiteForced
    ; suiteForcedᵈ = ObservationInitialityTheory.SuiteForcedᵈ
    ; codeRefineForced = ObservationInitialityTheory.CodeRefineForced
    ; morRefineForced∂ = ObservationInitialityTheory.MorRefineForced∂
    ; morRefineForced = ObservationInitialityTheory.MorRefineForced
    ; kernelHomFactorises = ArchitectureImplementationLaw.kernelHomLike≈-factorises
    ; implementationTotalisation = ArchitectureImplementationLaw.LOGArchitectureImplementation-isDecorated
    ; total⊑→base⊑ = Totalisation.total⊑→base⊑
    ; base⊑→total⊑ = Totalisation.base⊑→total⊑
    ; total≈→base≈ = Totalisation.total≈→base≈
    ; base≈→total≈ = Totalisation.base≈→total≈
    ; supportedArchitectureLayers = PortsAsDisplayed.supportedArchitectureLayers
    }
