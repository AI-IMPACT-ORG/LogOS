{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.ReifiedTower where

-- A curated adapter around `Stack.AsymptoticReification`.
--
-- This module is intentionally strict about epistemic status:
-- it does not claim to derive ZF(C) from weak axioms. Instead it packages a
-- boundary-level reification doctrine plus explicit stability obligations as a
-- route to a first-order ZFC stack (`ZFCStackFO`).
--
-- Any remaining set-theoretic strength (ω/Infinity/Foundation/Choice) is kept
-- as explicit parameters so downstream users can audit what is assumed beyond
-- the reification/stability machinery packaged here.

open import LogOS.Prelude
import LogOS.Apps.ZFC.Stack.AsymptoticReification as AR
import LogOS.Apps.ZFC.Stack.AsymptoticInfinityUpgrade as Inf
import LogOS.Apps.ZFC.Stack.FoundationUpgradeFO as FndFO
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO
import LogOS.Apps.ZFC.Stack.WellFoundedPart as WFPart
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

record ReifiedZFCFO
  {ℓ : Level}
  (C : ZF.SetContext {ℓ})
  (R : AR.PredicateReification C)
  : Set (lsuc (lsuc ℓ)) where

  module Core = AR.Core C R

  field
    -- Core constructor stability (Pair/Union/Powerset) for the chosen `Flow`.
    coreStability : Core.CoreStability

    -- ω/Infinity are kept explicit: this module only repackages them into a
    -- `ZFStackBase` once the reified core/powerset profiles exist.
    omegaSig : ZF.ZFSignatureOmega C
    infinityLaws : ZF.ZFLawsInfinity C Core.coreSigᵣ omegaSig

  base : Tower.ZFStackBase {ℓ}
  base =
    Core.zfStackBaseFromReification
      coreStability
      omegaSig
      infinityLaws

  module FO = AR.FO base R
  module WF = WFPart.ForBase base

  field
    -- FO-definable stability (needed for formula-coded Separation/Replacement).
    foStability : FO.FOStability

    -- Choice as an explicit upgrade over the pairing fragment.
    choiceUpgrade : Tower.ChoiceUpgrade (TowerFO.pairingStackFromBase base)

    -- Closure of the “well-founded part” universe under ω.
    wfClosure : WF.C.BaseWFClosure

  zfFO₋Fnd : TowerFO.ZFStackFO₋Fnd {ℓ}
  zfFO₋Fnd = FO.zfStackFO₋FndFromReification foStability

  module Fnd = FndFO.For zfFO₋Fnd

  field
    -- Foundation is constructed as an explicit upgrade step.
    foundationAssumptions : Fnd.FoundationAssumptions

  foundationUpgrade : Tower.FoundationUpgrade base
  foundationUpgrade = Fnd.foundationUpgrade foundationAssumptions

  -- The “well-founded part” of the base universe (sets equipped with `Acc _∈_`).
  baseᵂ : Tower.ZFStackBase {ℓ}
  baseᵂ = WF.baseᵂ wfClosure

  stackFO₋Fnd : TowerFO.ZFCStackFO₋Fnd {ℓ}
  stackFO₋Fnd = FO.zfcStackFO₋FndFromReification foStability choiceUpgrade

  stackFO : TowerFO.ZFCStackFO {ℓ}
  stackFO = FO.zfcStackFOFromReification foStability choiceUpgrade foundationUpgrade

-- Variant: discharge ω/Infinity via the ν fixed-point spine (`CoKleene`).
--
-- This replaces explicit ω/Infinity assumptions by:
-- - stability of the successor-image predicates used by `step`, and
-- - σ-directed completeness + σ-co-continuity assumptions for `step`.
record ReifiedZFCFOCoKleene
  {ℓ : Level}
  (C : ZF.SetContext {ℓ})
  (R : AR.PredicateReification C)
  : Set (lsuc (lsuc ℓ)) where

  module Core = AR.Core C R
  module I = Inf.For C R

  field
    infinityAssumptions : I.CoKleeneInfinityAssumptionsᵣ

  omegaSig : ZF.ZFSignatureOmega C
  omegaSig = I.omegaSig infinityAssumptions

  infinityLaws : ZF.ZFLawsInfinity C Core.coreSigᵣ omegaSig
  infinityLaws = I.infinityLaws infinityAssumptions

  base : Tower.ZFStackBase {ℓ}
  base =
    Core.zfStackBaseFromReification
      (I.CoKleeneInfinityAssumptionsᵣ.coreStability infinityAssumptions)
      omegaSig
      infinityLaws

  module FO = AR.FO base R
  module WF = WFPart.ForBase base

  field
    foStability : FO.FOStability
    choiceUpgrade : Tower.ChoiceUpgrade (TowerFO.pairingStackFromBase base)
    wfClosure : WF.C.BaseWFClosure

  zfFO₋Fnd : TowerFO.ZFStackFO₋Fnd {ℓ}
  zfFO₋Fnd = FO.zfStackFO₋FndFromReification foStability

  module Fnd = FndFO.For zfFO₋Fnd

  field
    foundationAssumptions : Fnd.FoundationAssumptions

  foundationUpgrade : Tower.FoundationUpgrade base
  foundationUpgrade = Fnd.foundationUpgrade foundationAssumptions

  baseᵂ : Tower.ZFStackBase {ℓ}
  baseᵂ = WF.baseᵂ wfClosure

  stackFO₋Fnd : TowerFO.ZFCStackFO₋Fnd {ℓ}
  stackFO₋Fnd = FO.zfcStackFO₋FndFromReification foStability choiceUpgrade

  stackFO : TowerFO.ZFCStackFO {ℓ}
  stackFO = FO.zfcStackFOFromReification foStability choiceUpgrade foundationUpgrade
