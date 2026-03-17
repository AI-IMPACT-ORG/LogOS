{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic where

-- MetaTheory — Foundational logic via mechanisable boundary semantics,
-- internal guarded self-reference, architectural normal form, and explicit
-- extensional collapse.
--
-- The main packaged object here is internal to the framework:
-- `MechanisableLogicWorld` packages the boundary world, complete-presentation
-- invariance, the homwise LT kernel internalisation of that world, the LT
-- architectural normal form, the internal guarded self-reference fibre of
-- each reflected hom, and fibrewise extensional reflection as one explicit
-- internal record.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; _≈_)
open import LogOS.LT.Coherence using (approx)
open import LogOS.LT.View using (View; _⊑[_]_)
open import LogOS.LT.Kernel using (Kernel; Code; CodePreorder; bnd; decode)
open import LogOS.LT.Hom.Core using (KernelHom; mapCode)
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
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; elem)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  ; BicatW→Thin2Cat
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  ; canonicalShadow
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView
  ; shadowFromView
  )

import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection
import LogOS.LT.Presentation as PresentationTheory
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.AbstractKZ as AbstractKZ
import LogOS.LT.Theorems.ArchitecturalNormalForm as ArchitecturalNormalForm
import LogOS.LT.LOG.QuotePort2Cat.Port as QuotePort
import LogOS.LT.Theorems.StableCompletion as StableCompletion
import LogOS.LT.Theorems.ExtensionalReflection as ExtensionalReflection
import LogOS.LT.Theorems.AbstractGaloisConnection as Galois
import LogOS.LT.Theorems.Centering as Centering
import LogOS.Ports.Reification.GuardedLawvere as GuardedLawvere

BoundarySemanticsAt
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
  → (S : ShadowByView (BicatW→TwoCellOps B) O)
  → (A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B))
  → ConPreorder ℓOCon ℓORel
BoundarySemanticsAt S A₀ B₀ =
  bnd (ObservationReflection.BoundaryKernelAt S {A = A₀} {B = B₀})

record BoundarySelfReferenceFibre
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  (S : ShadowByView (BicatW→TwoCellOps B) O)
  (A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B))
  (GC : GuardedClosure (BoundarySemanticsAt {B = B} {O = O} S A₀ B₀))
  : Setω where

  boundaryCP
    : ConPreorder ℓOCon ℓORel
  boundaryCP = BoundarySemanticsAt {B = B} {O = O} S A₀ B₀

  boundaryKernel
    : Kernel ℓOCon ℓORel ℓHom₁
  boundaryKernel = ObservationReflection.BoundaryKernelAt S {A = A₀} {B = B₀}

  boundaryKZ
    : AbstractKZ.KZModality boundaryCP
  boundaryKZ = record { GC = GC }

  stableCompletion
    : KernelHom boundaryKernel (QuotePort.quoteKernel GC)
  stableCompletion = StableCompletion.stableCompletion boundaryKernel GC

  stableCompletion-law
    : ∀ γ
    → _≈_ boundaryCP
        (decode (QuotePort.quoteKernel GC) (mapCode stableCompletion γ))
        (Flow GC (decode boundaryKernel γ))
  stableCompletion-law = StableCompletion.stableCompletion-law {m = approx} boundaryKernel GC

  lawvereStableFixedPoint
    : ∀ {ℓA ℓX : Level}
        {A : Set ℓA}
        {X : Set ℓX}
        {E : GuardedLawvere.StableEvaluator A X boundaryCP GC}
    → (Q : GuardedLawvere.QuotedPointSurjective E)
    → (α : Stable {CP = boundaryCP} (Flow GC)
         → Stable {CP = boundaryCP} (Flow GC))
    → Σ (Stable {CP = boundaryCP} (Flow GC))
        (λ p → _≈_ boundaryCP (elem p) (elem (α p)))
  lawvereStableFixedPoint = GuardedLawvere.lawvereStableFixedPoint

  lawvereObstruction
    : ∀ {ℓA ℓX : Level}
        {A : Set ℓA}
        {X : Set ℓX}
        {E : GuardedLawvere.StableEvaluator A X boundaryCP GC}
    → Σ
        (Stable {CP = boundaryCP} (Flow GC)
           → Stable {CP = boundaryCP} (Flow GC))
        (λ α → ∀ p → ¬ _≈_ boundaryCP (elem p) (elem (α p)))
    → ¬ GuardedLawvere.QuotedPointSurjective E
  lawvereObstruction = GuardedLawvere.noStableFixedPoint-obstructsQuotedPointSurjective

record MechanisableLogicWorld
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  (B : BicatW ℓObj ℓHom₁ ℓHom₂)
  (O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel)
  (S : ShadowByView (BicatW→TwoCellOps B) O)
  : Setω where

  field
    boundarySemantics
      : ObservationReflection.BoundarySemanticsTheorem B O S

    anf
      : ∀ {ℓ ℓRel ℓCode : Level}
      → ArchitecturalNormalForm.ObservationPreservingArchitecturalNormalForm ℓ ℓRel ℓCode

    extensionalInclude
      : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
          {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
      → Thin2Functor
          (ExtensionalReflection.ExtensionalFiber D)
          (ExtensionalReflection.ObservationFirstFiber D)

    extensionalReflect
      : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
          {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
        → Thin2Functor
            (ExtensionalReflection.ObservationFirstFiber D)
            (ExtensionalReflection.ExtensionalFiber D)

    homwiseExtensionalReflection
      : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
          {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
          (X : ExtensionalReflection.ObservationObj D)
          (Y : ExtensionalReflection.ExtensionalObj D)
        → Galois.GaloisConnection
            (ExtensionalReflection.ObservationHomPreorder D X Y)
            (ExtensionalReflection.ExtensionalHomPreorder D X Y)

  boundaryWorld
    : Thin2Cat ℓObj ℓHom₁ ℓORel
  boundaryWorld =
    ObservationReflection.BoundarySemanticsTheorem.boundaryWorld boundarySemantics

  boundaryWorld-isCanonical
    : boundaryWorld ≡ ObservationReflection.BoundaryWorld S
  boundaryWorld-isCanonical = refl

  reflectIntoBoundaryWorld
    : Thin2Functor
        (BicatW→Thin2Cat B)
        boundaryWorld
  reflectIntoBoundaryWorld =
    ObservationReflection.BoundarySemanticsTheorem.reflectIntoBoundaryWorld boundarySemantics

  canonical≤boundaryWorld
    : Shadow≤
        (canonicalShadow (BicatW→TwoCellOps B))
        (shadowFromView S)
  canonical≤boundaryWorld =
    ObservationReflection.BoundarySemanticsTheorem.canonical≤boundary boundarySemantics

  boundaryKernelAt
    : ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
    → Kernel ℓOCon ℓORel ℓHom₁
  boundaryKernelAt {A₀} {B₀} =
    ObservationReflection.BoundarySemanticsTheorem.boundaryKernelAt boundarySemantics {A₀} {B₀}

  boundaryHom-isCodePreorder
    : ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
    → ObservationReflection.BoundaryHomPreorder S A₀ B₀
      ≡ CodePreorder (ObservationReflection.BoundaryKernelAt S {A₀} {B₀})
  boundaryHom-isCodePreorder {A₀} {B₀} =
    ObservationReflection.BoundarySemanticsTheorem.boundaryHom-isCodePreorder boundarySemantics {A₀} {B₀}

  boundaryPresentationShadow
    : (P : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → RefinementShadow {ℓRel = ℓORel} (BicatW→TwoCellOps B)
  boundaryPresentationShadow =
    ObservationReflection.BoundarySemanticsTheorem.presentedShadow boundarySemantics

  boundaryPresentationWorld
    : (P : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → Thin2Cat ℓObj ℓHom₁ ℓORel
  boundaryPresentationWorld =
    ObservationReflection.BoundarySemanticsTheorem.boundaryPresentationWorld boundarySemantics

  boundaryPresentationWorld-isCanonical
    : (P : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → boundaryPresentationWorld P CP
      ≡ ObservationReflection.BoundaryPresentationWorld P CP
  boundaryPresentationWorld-isCanonical _ _ = refl

  boundaryPresentation≤boundaryWorld
    : (P : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → Shadow≤ (boundaryPresentationShadow P CP) (shadowFromView S)
  boundaryPresentation≤boundaryWorld =
    ObservationReflection.BoundarySemanticsTheorem.presentedShadow≤boundary boundarySemantics

  boundaryWorld≤boundaryPresentation
    : (P : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → Shadow≤ (shadowFromView S) (boundaryPresentationShadow P CP)
  boundaryWorld≤boundaryPresentation =
    ObservationReflection.BoundarySemanticsTheorem.boundary≤presentedShadow boundarySemantics

  completeBoundaryPresentationsEquivalent
    : (P : ObservationReflection.BoundaryPresentation S)
    → (Q : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → (CQ : ObservationReflection.CompleteBoundaryPresentation Q)
    → ObservationReflection.CompleteBoundaryPresentationsEquivalent P Q CP CQ
  completeBoundaryPresentationsEquivalent =
    ObservationReflection.BoundarySemanticsTheorem.completeBoundaryPresentationsEquivalent boundarySemantics

  completeBoundaryPresentationPackage
    : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel))
  completeBoundaryPresentationPackage =
    ObservationReflection.CompleteBoundaryPresentationPackage S

  canonicalCompleteBoundaryPresentationPackage
    : completeBoundaryPresentationPackage
  canonicalCompleteBoundaryPresentationPackage =
    ObservationReflection.canonicalCompleteBoundaryPresentationPackage S

  completeBoundaryPresentationFiber
    : Centering.ContractibleFiber
        completeBoundaryPresentationPackage
        ObservationReflection.CompleteBoundaryPresentationPackage≈
  completeBoundaryPresentationFiber =
    ObservationReflection.completeBoundaryPresentationFiber S

  completeBoundaryPresentationNoFork
    : Centering.NoSemanticFork
        ObservationReflection.CompleteBoundaryPresentationPackage≈
  completeBoundaryPresentationNoFork =
    ObservationReflection.completeBoundaryPresentationNoFork S

  presented↔boundaryKernelCanonical
    : (P : ObservationReflection.BoundaryPresentation S)
    → (CP : ObservationReflection.CompleteBoundaryPresentation P)
    → ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
        {f g : TwoCellOps.Hom₁ (BicatW→TwoCellOps B) A₀ B₀}
    → PresentationTheory.Presentation._≼_ (ObservationReflection.presentationAt P {A₀} {B₀}) f g
      ↔ _⊑_ (CodePreorder (ObservationReflection.BoundaryKernelAt S {A₀} {B₀})) f g
  presented↔boundaryKernelCanonical =
    ObservationReflection.BoundarySemanticsTheorem.presented↔boundaryKernelCanonical boundarySemantics

  extensionalReflectionUnit
    : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
        {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
        (X : ExtensionalReflection.ObservationObj D)
        (Y : ExtensionalReflection.ExtensionalObj D)
      → ∀ h
      → _⊑_ (ExtensionalReflection.ObservationHomPreorder D X Y)
          h
          (Galois.R (homwiseExtensionalReflection {D = D} X Y)
             (Galois.L (homwiseExtensionalReflection {D = D} X Y) h))
  extensionalReflectionUnit X Y =
    Galois.unit (homwiseExtensionalReflection X Y)

  extensionalReflectionCounit
    : ∀ {ℓ ℓRel ℓCode ℓDObj ℓDHom : Level}
        {D : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj ℓDHom}
        (X : ExtensionalReflection.ObservationObj D)
        (Y : ExtensionalReflection.ExtensionalObj D)
      → ∀ h
      → _⊑_ (ExtensionalReflection.ExtensionalHomPreorder D X Y)
          (Galois.L (homwiseExtensionalReflection {D = D} X Y)
             (Galois.R (homwiseExtensionalReflection {D = D} X Y) h))
          h
  extensionalReflectionCounit X Y =
    Galois.counit (homwiseExtensionalReflection X Y)

  boundarySelfReference
    : ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
    → (GC : GuardedClosure (BoundarySemanticsAt {B = B} {O = O} S A₀ B₀))
    → BoundarySelfReferenceFibre {B = B} {O = O} S A₀ B₀ GC
  boundarySelfReference {A₀} {B₀} GC = record {}

mechanisableLogicWorld
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
    (S : ShadowByView (BicatW→TwoCellOps B) O)
  → MechanisableLogicWorld B O S
mechanisableLogicWorld {B = B} S =
  let
    BST : ObservationReflection.BoundarySemanticsTheorem B _ S
    BST = ObservationReflection.boundarySemanticsTheorem {B = B} S
  in
  record
    { boundarySemantics = BST
    ; anf = ArchitecturalNormalForm.architecturalNormalForm
    ; extensionalInclude = λ {D = D} → ExtensionalReflection.includeExtensional {D = D}
    ; extensionalReflect = λ {D = D} → ExtensionalReflection.strictifyFiber {D = D}
    ; homwiseExtensionalReflection =
        λ {D = D} X Y → ExtensionalReflection.homwiseExtensionalReflection {D = D} X Y
    }

FoundationalLogicTheorem = MechanisableLogicWorld

foundationalLogicTheorem = mechanisableLogicWorld

MechanisableBoundarySemanticsTheorem = MechanisableLogicWorld

mechanisableBoundarySemanticsTheorem = mechanisableLogicWorld
