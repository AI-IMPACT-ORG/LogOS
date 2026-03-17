{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Mechanisable where

-- Strong downstream mechanisability as an apps-side adjective.
--
-- This module keeps the direct consequence functions and constructors for the
-- downstream mechanisable package separate from the later local symmetry
-- theorems. That split matches the mathematics more closely: first fix the
-- downstream adjective, then prove what it forces on one recognised image.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
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

open import LogOS.Apps.Summit.Policy using (GeneralisationPolicy; ObstructionPolicy)
open import LogOS.Apps.Summit.Recognition using
  ( MechanisableFragment
  ; fragmentGeneralisationPolicy
  ; recogniseMechanisableFragment
  )
open import LogOS.Apps.Summit.Quantitative using
  ( QuantitativeSummit )
open import LogOS.Apps.Summit.Obstruction using
  ( MechanisabilityObstruction
  ; obstructionOnMechanisableFragment
  )

record MechanisableDownstream
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {M : FoundationalLogic.MechanisableLogicWorld B O S}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  (D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂)
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
  : Setω where
  field
    generalisation : GeneralisationPolicy M D
    quantitative : QuantitativeSummit T Good Obs L P N
    obstructionPolicy : ObstructionPolicy M

  fragment : MechanisableFragment D
  fragment = recogniseMechanisableFragment generalisation

  diagonalObstruction
    : MechanisabilityObstruction fragment
  diagonalObstruction =
    obstructionOnMechanisableFragment fragment obstructionPolicy

  noFreeQuotedSelfReference
    = MechanisabilityObstruction.noFreeQuotedSelfReference
        diagonalObstruction

mechanisableRecognition
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {M : FoundationalLogic.MechanisableLogicWorld B O S}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
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
  → MechanisableDownstream {M = M} D T Good Obs L P N
  → MechanisableFragment D
mechanisableRecognition =
  MechanisableDownstream.fragment

mechanisableQuantitative
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {M : FoundationalLogic.MechanisableLogicWorld B O S}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
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
  → MechanisableDownstream {M = M} D T Good Obs L P N
  → QuantitativeSummit T Good Obs L P N
mechanisableQuantitative =
  MechanisableDownstream.quantitative

mechanisableObstruction
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {M : FoundationalLogic.MechanisableLogicWorld B O S}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
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
  → (mechanisable : MechanisableDownstream {M = M} D T Good Obs L P N)
  → MechanisabilityObstruction (mechanisableRecognition mechanisable)
mechanisableObstruction =
  MechanisableDownstream.diagonalObstruction

atLeastAsStrongAsMechanisable→mechanisable
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {M : FoundationalLogic.MechanisableLogicWorld B O S}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
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
  → (GP : GeneralisationPolicy M D)
  → QuantitativeSummit T Good Obs L P N
  → ObstructionPolicy M
  → MechanisableDownstream D T Good Obs L P N
atLeastAsStrongAsMechanisable→mechanisable GP quantitative policy =
  record
    { generalisation = GP
    ; quantitative = quantitative
    ; obstructionPolicy = policy
    }

fragment→mechanisable
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
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
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → QuantitativeSummit T Good Obs L P N
  → ObstructionPolicy (MechanisableFragment.seed F)
  → MechanisableDownstream {M = MechanisableFragment.seed F} D T Good Obs L P N
fragment→mechanisable F quantitative policy =
  atLeastAsStrongAsMechanisable→mechanisable
    (fragmentGeneralisationPolicy F)
    quantitative
    policy
