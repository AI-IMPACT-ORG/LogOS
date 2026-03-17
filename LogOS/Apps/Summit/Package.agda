{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Package where

-- Fixed-payload summit packages over one recognised image.
--
-- The quantitative and obstruction payload are determined by mechanisability.
-- Over one recognised image, the only remaining degree of freedom is the
-- shared-boundary complete presentation. The package-level no-fork and
-- weak-terminal statements below make that explicit.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Presentation using (Presentation)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
open import LogOS.Ports.Opacity.ObservationAction using (ObservationAction)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.Valuation.AbstractQuanticNucleus using (QuanticNucleus)

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

open import LogOS.Apps.Summit.Policy using (ObstructionPolicy)
open import LogOS.Apps.Summit.Mechanisable using
  ( MechanisableDownstream
  )
open import LogOS.Apps.Summit.Recognition using
  ( MechanisableFragment
  )
open import LogOS.Apps.Summit.Admissibility using (ObservationalSufficiency)
open import LogOS.Apps.Summit.Quantitative using
  ( QuantitativeSummit )
open import LogOS.Apps.Summit.Obstruction using
  ( MechanisabilityObstruction
  ; obstructionOnMechanisableFragment
  )
open import LogOS.Apps.Summit.Image using
  ( SymmetryRespectingMechanisableImage
  ; symmetryRespecting→noForkOnImage
  ; symmetryRespecting→weakTerminalOnImage
  )

SymmetryRespectingSummitPayload :
  ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
    {B : BicatW ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
       → TwoCellOps.Obj (BicatW→TwoCellOps B)
       → ConPreorder ℓOCon ℓORel}
    {S : ShadowByView (BicatW→TwoCellOps B) O}
    {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
    {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
    {ℓA : Level}
  → (SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA)
  → {ℓTCon ℓTRel ℓP : Level}
    {ℓObsCon ℓObsRel : Level}
    {ℓScaleCon ℓScaleRel : Level}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    {ℓLabel : Level}
  → (T : ConPreorder ℓTCon ℓTRel)
  → (Good : Con T → Set ℓP)
  → (Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D)
  → (L : LandauerAssumptions D Scale JP)
  → (P : Set ℓLabel)
  → (N : QuanticNucleus JP)
  → Setω
SymmetryRespectingSummitPayload {D = D} SR T Good Obs L P N =
  MechanisableDownstream
    {M = MechanisableFragment.seed
            (SymmetryRespectingMechanisableImage.fragment SR)}
    D
    T
    Good
    Obs
    L
    P
    N

mechanisablePayloadOnImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
  → (SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA)
  → {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
  → MechanisableDownstream
      {M = MechanisableFragment.seed
              (SymmetryRespectingMechanisableImage.fragment SR)}
      D
      T
      Good
      Obs
      L
      P
      N
  → SymmetryRespectingSummitPayload SR T Good Obs L P N
mechanisablePayloadOnImage _ mechanisable = mechanisable

record SymmetryRespectingSummitPackage
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  {ℓA : Level}
  (SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA)
  {ℓTCon ℓTRel ℓP : Level}
  (T : ConPreorder ℓTCon ℓTRel)
  (Good : Con T → Set ℓP)
  {ℓObsCon ℓObsRel : Level}
  {ℓScaleCon ℓScaleRel : Level}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  (Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D)
  (L : LandauerAssumptions D Scale JP)
  {ℓLabel : Level}
  (P : Set ℓLabel)
  (N : QuanticNucleus JP)
  (payload : SymmetryRespectingSummitPayload SR T Good Obs L P N)
  : Setω where
  field
    sharedBoundaryPresentation
      : ObservationReflection.CompleteBoundaryPresentationPackage S

  presentation : ObservationReflection.BoundaryPresentation S
  presentation = proj₁ sharedBoundaryPresentation

  completePresentation : ObservationReflection.CompleteBoundaryPresentation presentation
  completePresentation = proj₂ sharedBoundaryPresentation

  fragment : MechanisableFragment D
  fragment = SymmetryRespectingMechanisableImage.fragment SR

  admissibility : ObservationalSufficiency fragment ℓA
  admissibility = SymmetryRespectingMechanisableImage.admissibility SR

  quantitative : QuantitativeSummit T Good Obs L P N
  quantitative = MechanisableDownstream.quantitative payload

  obstructionPolicy
    : ObstructionPolicy
        (MechanisableFragment.seed
          (SymmetryRespectingMechanisableImage.fragment SR))
  obstructionPolicy = MechanisableDownstream.obstructionPolicy payload

  mechanisable
    : MechanisableDownstream
        {M = MechanisableFragment.seed fragment}
        D
        T
        Good
        Obs
        L
        P
        N
  mechanisable = payload

  obstruction
    : MechanisabilityObstruction fragment
  obstruction = obstructionOnMechanisableFragment fragment obstructionPolicy

SummitPackageOnImage≈
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
  → SymmetryRespectingSummitPackage SR T Good Obs L P N payload
  → SymmetryRespectingSummitPackage SR T Good Obs L P N payload
  → Set _
SummitPackageOnImage≈ X Y =
  ObservationReflection.CompleteBoundaryPresentationPackage≈
    (SymmetryRespectingSummitPackage.sharedBoundaryPresentation X)
    (SymmetryRespectingSummitPackage.sharedBoundaryPresentation Y)

canonicalSymmetryRespectingSummitPackage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
  → (SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA)
  → {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
  → (payload : SymmetryRespectingSummitPayload SR T Good Obs L P N)
  → SymmetryRespectingSummitPackage SR T Good Obs L P N payload
canonicalSymmetryRespectingSummitPackage SR payload =
  record
    { sharedBoundaryPresentation =
        ObservationReflection.canonicalCompleteBoundaryPresentationPackage _
    }

summitPackage→noForkOnImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
  → (X Y : SymmetryRespectingSummitPackage SR T Good Obs L P N payload)
  → ∀ {A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)}
      {f g : Con (Thin2Cat.Hom
                  (FoundationalLogic.MechanisableLogicWorld.boundaryWorld
                    (MechanisableFragment.seed
                      (SymmetryRespectingMechanisableImage.fragment SR)))
                  A₀
                  B₀)}
  → ObservationalSufficiency.VisibleRefinementOnImage
      (SymmetryRespectingMechanisableImage.admissibility SR)
      f
      g
  → Presentation._≼_
      (ObservationReflection.presentationAt
        (SymmetryRespectingSummitPackage.presentation X)
        {A₀}
        {B₀})
      f
      g
    ×
    Presentation._≼_
      (ObservationReflection.presentationAt
        (SymmetryRespectingSummitPackage.presentation Y)
        {A₀}
        {B₀})
      f
      g
summitPackage→noForkOnImage {SR = SR} X Y visible =
  symmetryRespecting→noForkOnImage
    SR
    (SymmetryRespectingSummitPackage.presentation X)
    (SymmetryRespectingSummitPackage.presentation Y)
    (SymmetryRespectingSummitPackage.completePresentation X)
    (SymmetryRespectingSummitPackage.completePresentation Y)
    visible

summitPackageAgreement→presentationAgreement
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
      {X Y : SymmetryRespectingSummitPackage SR T Good Obs L P N payload}
  → SummitPackageOnImage≈ X Y
  → ObservationReflection.CompleteBoundaryPresentationPackage≈
      (SymmetryRespectingSummitPackage.sharedBoundaryPresentation X)
      (SymmetryRespectingSummitPackage.sharedBoundaryPresentation Y)
summitPackageAgreement→presentationAgreement XY = XY

presentationAgreement→summitPackageAgreement
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
      {X Y : SymmetryRespectingSummitPackage SR T Good Obs L P N payload}
  → ObservationReflection.CompleteBoundaryPresentationPackage≈
      (SymmetryRespectingSummitPackage.sharedBoundaryPresentation X)
      (SymmetryRespectingSummitPackage.sharedBoundaryPresentation Y)
  → SummitPackageOnImage≈ X Y
presentationAgreement→summitPackageAgreement XY = XY
payloadOnImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
  → SymmetryRespectingSummitPackage SR T Good Obs L P N payload
  → SymmetryRespectingSummitPayload SR T Good Obs L P N
payloadOnImage X = SymmetryRespectingSummitPackage.mechanisable X

summitPackage→weakTerminalOnImage
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
  → (X : SymmetryRespectingSummitPackage SR T Good Obs L P N payload)
  → SummitPackageOnImage≈
      X
      (canonicalSymmetryRespectingSummitPackage SR payload)
summitPackage→weakTerminalOnImage {SR = SR} X =
  symmetryRespecting→weakTerminalOnImage
    SR
    (SymmetryRespectingSummitPackage.presentation X)
    (SymmetryRespectingSummitPackage.completePresentation X)

summitPackages→sameImagePresentation
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
      {ℓA : Level}
      {SR : SymmetryRespectingMechanisableImage {B = B} {O = O} {S = S} D ℓA}
      {ℓTCon ℓTRel ℓP : Level}
      {T : ConPreorder ℓTCon ℓTRel}
      {Good : Con T → Set ℓP}
      {ℓObsCon ℓObsRel : Level}
      {ℓScaleCon ℓScaleRel : Level}
      {Scale : ConPreorder ℓScaleCon ℓScaleRel}
      {JP : JoinPrequantale Scale}
      {Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} D}
      {L : LandauerAssumptions D Scale JP}
      {ℓLabel : Level}
      {P : Set ℓLabel}
      {N : QuanticNucleus JP}
      {payload : SymmetryRespectingSummitPayload SR T Good Obs L P N}
  → (X Y : SymmetryRespectingSummitPackage SR T Good Obs L P N payload)
  → SummitPackageOnImage≈ X Y
summitPackages→sameImagePresentation X Y =
  ObservationReflection.completeBoundaryPresentationPackage≈-trans
    (summitPackage→weakTerminalOnImage X)
    (ObservationReflection.completeBoundaryPresentationPackage≈-sym
      (summitPackage→weakTerminalOnImage Y))
