{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Obstruction where

-- Diagonal obstruction over a recognised mechanisable fragment.
--
-- This module does not transport obstruction automatically through arbitrary
-- functors. The extra quoted/self-reference witness is explicit, but it is now
-- read as structure on a recognised mechanisable fragment rather than as a
-- free-standing summit input.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView )
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.Ports.Reification.GuardedLawvere as GuardedLawvere

open import LogOS.Apps.Summit.Policy using (ObstructionPolicy)
open import LogOS.Apps.Summit.Recognition using
  ( MechanisableFragment
  )

record MechanisabilityObstruction
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  : Setω where
  field
    policy : ObstructionPolicy (MechanisableFragment.seed F)

  module Seed = FoundationalLogic.MechanisableLogicWorld (MechanisableFragment.seed F)
  module Policy = ObstructionPolicy policy

  selfReference
    : FoundationalLogic.BoundarySelfReferenceFibre
        {B = B}
        {O = O}
        S
        (Policy.A₀)
        (Policy.B₀)
        (Policy.guardedClosure)
  selfReference =
    Seed.boundarySelfReference (Policy.guardedClosure)

  lawvereObstruction
    : ¬ GuardedLawvere.QuotedPointSurjective (Policy.evaluator)
  lawvereObstruction =
    FoundationalLogic.BoundarySelfReferenceFibre.lawvereObstruction
      selfReference
      (Policy.obstructionData)

  noFreeQuotedSelfReference
    : ¬ GuardedLawvere.QuotedPointSurjective (Policy.evaluator)
  noFreeQuotedSelfReference = lawvereObstruction

obstructionOnMechanisableFragment
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
      {B : BicatW ℓObj ℓHom₁ ℓHom₂}
      {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
         → TwoCellOps.Obj (BicatW→TwoCellOps B)
         → ConPreorder ℓOCon ℓORel}
      {S : ShadowByView (BicatW→TwoCellOps B) O}
      {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
      {D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂}
  → (F : MechanisableFragment {B = B} {O = O} {S = S} D)
  → ObstructionPolicy (MechanisableFragment.seed F)
  → MechanisabilityObstruction F
obstructionOnMechanisableFragment F policy =
  record
    { policy = policy
    }
