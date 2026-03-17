{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Summit where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Presentation using (Presentation)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using
  ( ConservativeThin2Functor
  ; idConservativeThin2Functor
  )

open import LogOS.Ports.CriticalParameter using (CriticalCut; SharpCut)
open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
open import LogOS.Ports.Opacity.ObservationAction using (ObservationAction)
open import LogOS.Ports.AbstractLandauerObservational using
  ( ObservationalCostBridge )
open import LogOS.Ports.Opacity.Profile using (OpaqueAt)
open import LogOS.Ports.Universality.NatBoundary using (NatBoundary)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.AbstractQuanticNucleus using (QuanticNucleus)
import LogOS.Ports.Valuation.AbstractQuanticNucleus as Nucleus
import LogOS.Ports.Valuation.AbstractConnesKreimer as CK
import LogOS.LT.Theorems.AbstractGaloisConnection as Galois
import LogOS.Ports.Reification.GuardedLawvere as GuardedLawvere
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView )
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ObservationReflection.Core as ObservationReflection

import LogOS.Checks.FoundationalLogic as Base
import LogOS.Checks.QuantitativeThresholds as QT
import LogOS.Checks.Support.TrivialBoundaryWorld as Trivial

import LogOS.Apps.Summit.Policy as SummitPolicy
import LogOS.Apps.Summit.Recognition as SummitRecognition
import LogOS.Apps.Summit.Mechanisable as SummitMechanisable
import LogOS.Apps.Summit.Admissibility as SummitAdmissibility
import LogOS.Apps.Summit.Quantitative as SummitQuantitative
import LogOS.Apps.Summit.Obstruction as SummitObstruction
import LogOS.Apps.Summit.Image as SummitImage
import LogOS.Apps.Summit.Package as SummitPackage

module ≤-Reasoning = LogOS.Prelude.RefinementKit.Reasoning

BoundaryWorld : Thin2Cat lzero lzero lzero
BoundaryWorld = Base.FL.boundaryWorld

generalisationPolicy
  : SummitPolicy.GeneralisationPolicy Base.theorem BoundaryWorld
generalisationPolicy =
  record
    { generalise = idConservativeThin2Functor BoundaryWorld
    }

fragment
  : SummitRecognition.MechanisableFragment BoundaryWorld
fragment =
  SummitRecognition.recogniseMechanisableFragment generalisationPolicy

_ : ConservativeThin2Functor BoundaryWorld BoundaryWorld
_ = SummitRecognition.MechanisableFragment.generalisation fragment

_ : Galois.ReflectiveImageTheorem
      (Base.FL.homwiseExtensionalReflection {D = Base.trivialDisplayed} Base.X Base.Y)
_ = SummitRecognition.recognisedReflectiveImage fragment Base.X Base.Y

_ = SummitRecognition.recognisedPresentationInvariance
      fragment
      Trivial.P
      Trivial.P
      Trivial.CP
      Trivial.CP

admissibility
  : SummitAdmissibility.ObservationalSufficiency fragment lzero
admissibility =
  record
    { VisibleRefinement = λ {A} {B} h k → ConPreorder._⊑_ (Thin2Cat.Hom BoundaryWorld A B) h k
    ; visibleRefinement-sound = λ hk → hk
    ; visibleRefinement-extensional =
        λ {A} {B} h h' k k' (h≤h' , h'≤h) (k≤k' , k'≤k) hk →
          let
            CP = Thin2Cat.Hom BoundaryWorld A B
            module R = ≤-Reasoning CP
            step₁ : ConPreorder._⊑_ CP h' h
            step₁ = h'≤h
            step₂ : ConPreorder._⊑_ CP h k
            step₂ = hk
            step₃ : ConPreorder._⊑_ CP k k'
            step₃ = k≤k'
            step₁₂ : ConPreorder._⊑_ CP h' k
            step₁₂ = R._⊑⟨_⟩_ h' {b = h} {c = k} step₁ step₂
            step₁₂₃ : ConPreorder._⊑_ CP h' k'
            step₁₂₃ = R._⊑⟨_⟩_ h' {b = k} {c = k'} step₁₂ step₃
          in
          R.begin⊑_ {a = h'} {b = k'} step₁₂₃
    }

symmetryImage
  : SummitImage.SymmetryRespectingMechanisableImage BoundaryWorld lzero
symmetryImage =
  record
    { fragment = fragment
    ; admissibility = admissibility
    }

_ : Presentation._≼_ (ObservationReflection.presentationAt Trivial.P {tt} {tt}) tt tt
_ =
  SummitAdmissibility.ObservationalSufficiency.sharedBoundaryCollapse→canonicalCollapse
    admissibility
    {A₀ = tt}
    {B₀ = tt}
    {f = tt}
    {g = tt}
    tt

_ : Presentation._≼_ (ObservationReflection.presentationAt Trivial.P {tt} {tt}) tt tt
  × Presentation._≼_ (ObservationReflection.presentationAt Trivial.P {tt} {tt}) tt tt
_ =
  SummitImage.symmetryRespecting→noForkOnImage
    symmetryImage
    Trivial.P
    Trivial.P
    Trivial.CP
    Trivial.CP
    {A₀ = tt}
    {B₀ = tt}
    {f = tt}
    {g = tt}
    tt

_ : ObservationReflection.CompleteBoundaryPresentationPackage≈
      (Trivial.P , Trivial.CP)
      (ObservationReflection.canonicalCompleteBoundaryPresentationPackage Trivial.S)
_ =
  SummitImage.symmetryRespecting→weakTerminalOnImage
    symmetryImage
    Trivial.P
    Trivial.CP

module QuantitativeWitness
  {ℓObj ℓHomCon ℓHomRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {ℓObsCon ℓObsRel : Level}
  {ℓScaleCon ℓScaleRel : Level}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C}
  (L : LandauerAssumptions C Scale JP)
  {ℓLabel : Level}
  (P : Set ℓLabel)
  (N : QuanticNucleus JP)
  (Bridge : ObservationalCostBridge Obs L)
  where

  _ : SummitQuantitative.QuantitativeSummit
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
  _ =
    SummitQuantitative.quantitativeSummitFromSharpCut
      QT.sharpOpacityCut
      Bridge
      (Nucleus.QuanticNucleusLocal.leastStableMultiplicativeApproximation N)
      (CK.CK.stableConvolutionTheorem JP P N)

module ObstructionWitness
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  (fragment : SummitRecognition.MechanisableFragment {B = B} {O = O} {S = S} D)
  (policy : SummitPolicy.ObstructionPolicy
              (SummitRecognition.MechanisableFragment.seed fragment))
  where

  obstruction
    : SummitObstruction.MechanisabilityObstruction fragment
  obstruction =
    SummitObstruction.obstructionOnMechanisableFragment fragment policy

  _ : ¬ GuardedLawvere.QuotedPointSurjective
        (SummitPolicy.ObstructionPolicy.evaluator policy)
  _ = SummitObstruction.MechanisabilityObstruction.noFreeQuotedSelfReference obstruction

module FullSummitWitness
  {ℓScaleCon ℓScaleRel : Level}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  {ℓObsCon ℓObsRel : Level}
  {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} BoundaryWorld}
  (L : LandauerAssumptions BoundaryWorld Scale JP)
  {ℓLabel : Level}
  (P : Set ℓLabel)
  (N : QuanticNucleus JP)
  (Bridge : ObservationalCostBridge Obs L)
  (policy : SummitPolicy.ObstructionPolicy Base.theorem)
  where

  quantitative
    : SummitQuantitative.QuantitativeSummit
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
  quantitative =
    SummitQuantitative.quantitativeSummitFromSharpCut
      QT.sharpOpacityCut
      Bridge
      (Nucleus.QuanticNucleusLocal.leastStableMultiplicativeApproximation N)
      (CK.CK.stableConvolutionTheorem JP P N)

  mechanisable
    : SummitMechanisable.MechanisableDownstream
        BoundaryWorld
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
  mechanisable =
    SummitMechanisable.atLeastAsStrongAsMechanisable→mechanisable
      generalisationPolicy
      quantitative
      policy

  _ : SummitRecognition.MechanisableFragment BoundaryWorld
  _ = SummitMechanisable.mechanisableRecognition mechanisable

  _ : ¬ GuardedLawvere.QuotedPointSurjective
        (SummitPolicy.ObstructionPolicy.evaluator policy)
  _ = SummitMechanisable.MechanisableDownstream.noFreeQuotedSelfReference mechanisable

  payload
    : SummitPackage.SymmetryRespectingSummitPayload
        symmetryImage
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
  payload =
    mechanisable

  package
    : SummitPackage.SymmetryRespectingSummitPackage
        symmetryImage
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
        payload
  package =
    record
      { sharedBoundaryPresentation = Trivial.P , Trivial.CP
      }

  canonicalPackage
    : SummitPackage.SymmetryRespectingSummitPackage
        symmetryImage
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
        payload
  canonicalPackage =
    SummitPackage.canonicalSymmetryRespectingSummitPackage
      symmetryImage
      payload

  _ : ObservationReflection.CompleteBoundaryPresentationPackage≈
        (Trivial.P , Trivial.CP)
        (ObservationReflection.canonicalCompleteBoundaryPresentationPackage Trivial.S)
  _ =
    SummitPackage.summitPackage→weakTerminalOnImage package

  _ : ObservationReflection.CompleteBoundaryPresentationPackage≈
        (SummitPackage.SymmetryRespectingSummitPackage.sharedBoundaryPresentation package)
        (SummitPackage.SymmetryRespectingSummitPackage.sharedBoundaryPresentation canonicalPackage)
  _ =
    SummitPackage.summitPackages→sameImagePresentation package canonicalPackage

  _ : SummitPackage.SymmetryRespectingSummitPayload
        symmetryImage
        NatBoundary
        (OpaqueAt QT.toyProfile QT.twoPoints)
        Obs
        L
        P
        N
  _ =
    SummitPackage.payloadOnImage package

  _ : Presentation._≼_ (ObservationReflection.presentationAt Trivial.P {tt} {tt}) tt tt
      × Presentation._≼_
          (ObservationReflection.presentationAt
            (ObservationReflection.canonicalBoundaryPresentation Trivial.S)
            {tt}
            {tt})
          tt
          tt
  _ =
    SummitPackage.summitPackage→noForkOnImage
      package
      canonicalPackage
      {A₀ = tt}
      {B₀ = tt}
      {f = tt}
      {g = tt}
      tt
