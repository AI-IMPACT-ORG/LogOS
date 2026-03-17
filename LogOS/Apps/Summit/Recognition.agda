{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Recognition where

-- Recognition by conservative generalisation.
--
-- This module does not construct a mechanisable world from arbitrary
-- downstream data. It only says that once such a world is chosen and carried
-- conservatively into a downstream thin logic, the already-proved capstone
-- theorem families are available as one collected fragment.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (ConservativeThin2Functor)
open import LogOS.LT.DisplayedThin2Cat using (DisplayedThin2Cat)
open import LogOS.LT.Flow using (GuardedClosure)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView )
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.Theorems.ExtensionalReflection as ExtensionalReflection
import LogOS.LT.Theorems.AbstractGaloisConnection as Galois
import LogOS.LT.Theorems.Centering as Centering

open import LogOS.Apps.Summit.Policy using (GeneralisationPolicy)

record RecognisedPresentationSymmetry
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  (S : ShadowByView (BicatW→TwoCellOps B) O)
  : Setω where
  field
    -- The recognised fragment exposes one local/shared-boundary presentation
    -- symmetry object; the accessors below are only projections from this.
    invariance
      : (P : ObservationReflection.BoundaryPresentation S)
      → (Q : ObservationReflection.BoundaryPresentation S)
      → (CP : ObservationReflection.CompleteBoundaryPresentation P)
      → (CQ : ObservationReflection.CompleteBoundaryPresentation Q)
      → ObservationReflection.CompleteBoundaryPresentationsEquivalent P Q CP CQ

    fiber
      : Centering.ContractibleFiber
          (ObservationReflection.CompleteBoundaryPresentationPackage S)
          (ObservationReflection.CompleteBoundaryPresentationPackage≈ {S = S})

    noFork
      : Centering.NoSemanticFork
          (ObservationReflection.CompleteBoundaryPresentationPackage≈ {S = S})

record MechanisableFragment
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  (D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂)
  : Setω where
  field
    seed : FoundationalLogic.MechanisableLogicWorld B O S
    generalisation
      : ConservativeThin2Functor
          (FoundationalLogic.MechanisableLogicWorld.boundaryWorld seed)
          D
    presentationSymmetry : RecognisedPresentationSymmetry {B = B} {O = O} S

  module Seed = FoundationalLogic.MechanisableLogicWorld seed

  reflectiveImage
    : ∀ {ℓ ℓRel ℓCode ℓDObj' ℓDHom' : Level}
        {D' : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj' ℓDHom'}
        (X : ExtensionalReflection.ObservationObj D')
        (Y : ExtensionalReflection.ExtensionalObj D')
      → Galois.ReflectiveImageTheorem
          (Seed.homwiseExtensionalReflection {D = D'} X Y)
  reflectiveImage X Y =
    Galois.reflectiveImageTheorem (Seed.homwiseExtensionalReflection X Y)

  selfReference
    : ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
    → (GC : GuardedClosure
        (FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀))
    → FoundationalLogic.BoundarySelfReferenceFibre {B = B} {O = O} S A₀ B₀ GC
  selfReference = Seed.boundarySelfReference

  extensionalReflection
    : ∀ {ℓ ℓRel ℓCode ℓDObj' ℓDHom' : Level}
        {D' : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj' ℓDHom'}
        (X : ExtensionalReflection.ObservationObj D')
        (Y : ExtensionalReflection.ExtensionalObj D')
      → Galois.GaloisConnection
          (ExtensionalReflection.ObservationHomPreorder D' X Y)
          (ExtensionalReflection.ExtensionalHomPreorder D' X Y)
  extensionalReflection = Seed.homwiseExtensionalReflection

recogniseMechanisableFragment
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {M : FoundationalLogic.MechanisableLogicWorld B O S}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → GeneralisationPolicy M D
  → MechanisableFragment D
recogniseMechanisableFragment {B = B} {O = O} {S = S} {M = M} GP =
  let
    seedPresentationSymmetry : RecognisedPresentationSymmetry S
    seedPresentationSymmetry =
      record
        { invariance =
            FoundationalLogic.MechanisableLogicWorld.completeBoundaryPresentationsEquivalent M
        ; fiber =
            FoundationalLogic.MechanisableLogicWorld.completeBoundaryPresentationFiber M
        ; noFork =
            FoundationalLogic.MechanisableLogicWorld.completeBoundaryPresentationNoFork M
        }
  in
  record
    { seed = M
    ; generalisation = GeneralisationPolicy.generalise GP
    ; presentationSymmetry = seedPresentationSymmetry
    }

fragmentGeneralisationPolicy
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → GeneralisationPolicy (MechanisableFragment.seed F) D
fragmentGeneralisationPolicy F =
  record
    { generalise = MechanisableFragment.generalisation F
    }

recognisedBoundaryWorld
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → Thin2Cat ℓObj ℓHom₁ ℓORel
recognisedBoundaryWorld F =
  FoundationalLogic.MechanisableLogicWorld.boundaryWorld (MechanisableFragment.seed F)

recognisedPresentationInvariance
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → (P : ObservationReflection.BoundaryPresentation S)
  → (Q : ObservationReflection.BoundaryPresentation S)
  → (CP : ObservationReflection.CompleteBoundaryPresentation P)
  → (CQ : ObservationReflection.CompleteBoundaryPresentation Q)
  → ObservationReflection.CompleteBoundaryPresentationsEquivalent P Q CP CQ
recognisedPresentationInvariance F =
  RecognisedPresentationSymmetry.invariance
    (MechanisableFragment.presentationSymmetry F)

recognisedReflectiveImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → ∀ {ℓ ℓRel ℓCode ℓDObj' ℓDHom' : Level}
      {D' : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj' ℓDHom'}
      (X : ExtensionalReflection.ObservationObj D')
      (Y : ExtensionalReflection.ExtensionalObj D')
    → Galois.ReflectiveImageTheorem
        (MechanisableFragment.extensionalReflection F X Y)
recognisedReflectiveImage F =
  MechanisableFragment.reflectiveImage F

recognisedPresentationFiber
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → Centering.ContractibleFiber
      (ObservationReflection.CompleteBoundaryPresentationPackage S)
      ObservationReflection.CompleteBoundaryPresentationPackage≈
recognisedPresentationFiber F =
  RecognisedPresentationSymmetry.fiber
    (MechanisableFragment.presentationSymmetry F)

recognisedPresentationNoFork
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → Centering.NoSemanticFork
      ObservationReflection.CompleteBoundaryPresentationPackage≈
recognisedPresentationNoFork F =
  RecognisedPresentationSymmetry.noFork
    (MechanisableFragment.presentationSymmetry F)

recognisedPresentationSymmetry
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → RecognisedPresentationSymmetry {B = B} {O = O} S
recognisedPresentationSymmetry =
  MechanisableFragment.presentationSymmetry

recognisedSelfReference
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
      (GC : GuardedClosure
        (FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀))
    → FoundationalLogic.BoundarySelfReferenceFibre {B = B} {O = O} S A₀ B₀ GC
recognisedSelfReference F =
  MechanisableFragment.selfReference F

recognisedExtensionalReflection
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → ∀ {ℓ ℓRel ℓCode ℓDObj' ℓDHom' : Level}
      {D' : DisplayedThin2Cat (Kernel2Cat.LOG {ℓ} {ℓRel} {ℓCode}) ℓDObj' ℓDHom'}
      (X : ExtensionalReflection.ObservationObj D')
      (Y : ExtensionalReflection.ExtensionalObj D')
    → Galois.GaloisConnection
        (ExtensionalReflection.ObservationHomPreorder D' X Y)
        (ExtensionalReflection.ExtensionalHomPreorder D' X Y)
recognisedExtensionalReflection F =
  MechanisableFragment.extensionalReflection F
