{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.FoundationalLogic where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.ConPreorder.Antisymmetry using (Antisymmetry)
open import LogOS.LT.Kernel using (Kernel; BoundaryKernel; CodePreorder)
open import LogOS.LT.Hom.Core using (KernelHom; idKernelHom)
open import LogOS.LT.Presentation using (Presentation)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; mkTotalObjR
  ; mkTotalHomR
  )
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; idClosure; mkStable; elem)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW→Thin2Cat )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( shadowFromView )
open import LogOS.Checks.Support.TrivialBoundaryWorld using (B; O; S; P; CP)

import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.LT.Theorems.ArchitecturalNormalForm as ArchitecturalNormalForm
import LogOS.LT.Theorems.ExtensionalReflection as ExtensionalReflection
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat
import LogOS.LT.LOG.QuotePort2Cat.Port as QuotePort
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode
import LogOS.LT.Theorems.AbstractGaloisConnection as Galois
import LogOS.Ports.Reification.GuardedLawvere as GuardedLawvere

trivialDisplayed
  : DisplayedThin2Cat (Kernel2Cat.LOG {lzero} {lzero} {lzero}) lzero lzero
trivialDisplayed =
  record
    { Ob = λ _ → ⊤
    ; HomD = λ _ _ _ → ⊤
    ; idD = λ _ → tt
    ; compD = λ _ _ → tt
    }

topUnique : ∀ {x y : ⊤ {lzero}} → x ≡ y
topUnique {ttℓ} {ttℓ} = refl

antiUnit : Antisymmetry UnitPreorder₀
antiUnit = record { antisym = λ _ _ → topUnique }

K : Kernel lzero lzero lzero
K = BoundaryKernel UnitPreorder₀

theorem : FoundationalLogic.MechanisableLogicWorld B O S
theorem = FoundationalLogic.mechanisableLogicWorld {B = B} {O = O} S

module FL = FoundationalLogic.MechanisableLogicWorld theorem

module ANF =
  ArchitecturalNormalForm.ObservationPreservingArchitecturalNormalForm
    (FL.anf {lzero} {lzero} {lzero})

CP₀ : ConPreorder lzero lzero
CP₀ = FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S ttℓ ttℓ

GCu
  : GuardedClosure CP₀
GCu = idClosure CP₀

selfRef
  : FoundationalLogic.BoundarySelfReferenceFibre {B = B} {O = O} S ttℓ ttℓ GCu
selfRef = FL.boundarySelfReference {A₀ = ttℓ} {B₀ = ttℓ} GCu

module SR = FoundationalLogic.BoundarySelfReferenceFibre selfRef

X
  : ExtensionalReflection.ObservationObj trivialDisplayed
X = mkTotalObjR K (antiUnit , tt)

Y
  : ExtensionalReflection.ExtensionalObj trivialDisplayed
Y = mkTotalObjR K (antiUnit , (StrictDecode.strictDecodeUnit , tt))

obsId
  : Con (ExtensionalReflection.ObservationHomPreorder trivialDisplayed X Y)
obsId = mkTotalHomR (idKernelHom K) (tt , tt)

extId
  : Con (ExtensionalReflection.ExtensionalHomPreorder trivialDisplayed X Y)
extId = Galois.L (FL.homwiseExtensionalReflection {D = trivialDisplayed} X Y) obsId

_ : Thin2Functor
      (BicatW→Thin2Cat B)
      (FL.boundaryWorld)
_ = FL.reflectIntoBoundaryWorld

_ : ObservationReflection.CompleteBoundaryPresentationsEquivalent P P CP CP
_ = FL.completeBoundaryPresentationsEquivalent P P CP CP

_ : ObservationReflection.BoundaryHomPreorder S ttℓ ttℓ
    ≡ CodePreorder (ObservationReflection.BoundaryKernelAt S {A = ttℓ} {B = ttℓ})
_ = FL.boundaryHom-isCodePreorder {A₀ = ttℓ} {B₀ = ttℓ}

_ : Presentation._≼_ (ObservationReflection.presentationAt P {ttℓ} {ttℓ}) ttℓ ttℓ
    ↔ _⊑_ (CodePreorder (ObservationReflection.BoundaryKernelAt S {A = ttℓ} {B = ttℓ})) ttℓ ttℓ
_ = FL.presented↔boundaryKernelCanonical P CP {A₀ = ttℓ} {B₀ = ttℓ} {f = ttℓ} {g = ttℓ}

_ : ANF.implementationTotalisation ≡ refl
_ = refl

_ : Thin2Functor
      (ExtensionalReflection.ExtensionalFiber trivialDisplayed)
      (ExtensionalReflection.ObservationFirstFiber trivialDisplayed)
_ = FL.extensionalInclude {D = trivialDisplayed}

_ : _⊑_
      (ExtensionalReflection.ObservationHomPreorder trivialDisplayed X Y)
      obsId
      (Galois.R (FL.homwiseExtensionalReflection {D = trivialDisplayed} X Y) extId)
_ = FL.extensionalReflectionUnit {D = trivialDisplayed} X Y obsId

E
  : GuardedLawvere.StableEvaluator (Topℓ {lzero}) (Topℓ {lzero})
      CP₀
      GCu
E =
  record
    { eval = λ _ _ → mkStable ttℓ tt }

Q
  : GuardedLawvere.QuotedPointSurjective E
Q =
  record
    { quotePoint = λ _ → ttℓ
    ; namesEvery = λ φ → ttℓ , (λ _ → (tt , tt))
    }

idStable
  : Stable {CP = CP₀} (Flow GCu)
  → Stable {CP = CP₀} (Flow GCu)
idStable x = x

_ : KernelHom
      (ObservationReflection.BoundaryKernelAt S {A = ttℓ} {B = ttℓ})
      (QuotePort.quoteKernel GCu)
_ = SR.stableCompletion

_ : Σ
      (Stable {CP = CP₀} (Flow GCu))
      (λ p →
        LogOS.LT.ConPreorder._≈_
          CP₀
          (elem p)
          (elem (idStable p)))
_ = SR.lawvereStableFixedPoint Q idStable
