{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.LateCollapseTower where

open import LogOS.Prelude
open import LogOS.LT.View using (μ)
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort using (PredicateReification)
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility using
  ( StagedPredicateReification
  ; staged→restricted
  )

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CoreFromReification as CoreR
import LogOS.Apps.ZFC.Stack.AsymptoticReification.FOFromReification as FOR
import LogOS.Apps.ZFC.Stack.FoundationUpgradeFO as FndFO
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO
import LogOS.Apps.ZFC.Stack.ReifiedTower as RT
import LogOS.Apps.ZFC.Stack.WellFounded as WFd
import LogOS.Apps.ZFC.Stack.WellFoundedPart as WFPart
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
import LogOS.Apps.ZFC.Proof.Semantics.Core as SemCore

module For {ℓ : Level} (C : ZF.SetContext {ℓ}) (R : PredicateReification C) where
  module Core = CoreR.Core C R

  FlowCollapse : Set (lsuc ℓ)
  FlowCollapse = Core.FlowCollapse

  record BaseAssumptions : Set (lsuc (lsuc ℓ)) where
    field
      omegaSig : ZF.ZFSignatureOmega C
      infinityLaws : ZF.ZFLawsInfinity C Core.coreSigᵣ omegaSig

  module WithFlowCollapse (close : FlowCollapse) where
    coreStability : Core.CoreStability
    coreStability = Core.coreStabilityFromFlowCollapse close

    module ForBase (B₀ : BaseAssumptions) where
      open BaseAssumptions B₀ public

      base : Tower.ZFStackBase {ℓ}
      base =
        Core.zfStackBaseFromReification
          coreStability
          omegaSig
          infinityLaws

      module FO = FOR.FO base R
      module WF = WFPart.ForBase base
      module FndBase = FndFO.ForBase base

      wfClosure
        : ((x : Tower.ZFStackBase.SetU base) → WFd.Acc (Tower.ZFStackBase._∈_ base) x)
        → WF.C.BaseWFClosure
      wfClosure wfMem = WF.C.baseWFClosure (wfMem (μ (Tower.ZFStackBase.OmegaV base) tt))

      record StructuralAssumptions : Set (lsuc (lsuc ℓ)) where
        field
          choiceUpgrade : Tower.ChoiceUpgrade (TowerFO.pairingStackFromBase base)
          emptyOrElem : FndBase.EmptyOrElemUpgrade

      Assumptions : Set (lsuc (lsuc ℓ))
      Assumptions = StructuralAssumptions

      module WithFO
        (FOW : FO.FOWitnesses)
        (wfMem : (x : Tower.ZFStackBase.SetU base) → WFd.Acc (Tower.ZFStackBase._∈_ base) x)
        where

        foStability : FO.FOStability
        foStability = FO.foStabilityFromFlowCollapse close FOW

        zfFO₋Fnd : TowerFO.ZFStackFO₋Fnd {ℓ}
        zfFO₋Fnd = FO.zfStackFO₋FndFromReification foStability

        module Fnd = FndFO.For zfFO₋Fnd

        foundationAssumptions
          : Assumptions
          → Fnd.FoundationAssumptions
        foundationAssumptions A =
          Fnd.foundationAssumptions (StructuralAssumptions.emptyOrElem A) wfMem

        reifiedZFCFO
          : Assumptions
          → RT.ReifiedZFCFO C R
        reifiedZFCFO A =
          record
            { coreStability = coreStability
            ; omegaSig = omegaSig
            ; infinityLaws = infinityLaws
            ; foStability = foStability
            ; choiceUpgrade = StructuralAssumptions.choiceUpgrade A
            ; wfClosure = wfClosure wfMem
            ; foundationAssumptions = foundationAssumptions A
            }

        baseᵂ : Assumptions → Tower.ZFStackBase {ℓ}
        baseᵂ A = RT.ReifiedZFCFO.baseᵂ (reifiedZFCFO A)

        stackFO₋Fnd : Assumptions → TowerFO.ZFCStackFO₋Fnd {ℓ}
        stackFO₋Fnd A = RT.ReifiedZFCFO.stackFO₋Fnd (reifiedZFCFO A)

        stackFO : Assumptions → TowerFO.ZFCStackFO {ℓ}
        stackFO A = RT.ReifiedZFCFO.stackFO (reifiedZFCFO A)

        proofModel : Assumptions → SemCore.Model {ℓ}
        proofModel A = SemCore.fromStackFO (stackFO A)

-- Native staged entrypoint: consume a staged admissibility ledger directly and
-- only forget to the restricted interface inside the generic tower composer.
module ForStaged {ℓ : Level} (C : ZF.SetContext {ℓ}) (S : StagedPredicateReification C) where
  private
    R : PredicateReification C
    R = staged→restricted S

  module Base = For C R

  FlowCollapse : Set (lsuc ℓ)
  FlowCollapse = Base.FlowCollapse

  BaseAssumptions : Set (lsuc (lsuc ℓ))
  BaseAssumptions = Base.BaseAssumptions

  module WithFlowCollapse (close : FlowCollapse) where
    module Impl = Base.WithFlowCollapse close

    module ForBase (B₀ : BaseAssumptions) where
      module Inner = Impl.ForBase B₀
      module FO = FOR.StagedFO Inner.base S
      module WF = Inner.WF

      base : Tower.ZFStackBase {ℓ}
      base = Inner.base

      StructuralAssumptions : Set (lsuc (lsuc ℓ))
      StructuralAssumptions = Inner.StructuralAssumptions

      Assumptions : Set (lsuc (lsuc ℓ))
      Assumptions = Inner.Assumptions

      wfClosure
        : ((x : Tower.ZFStackBase.SetU base) → WFd.Acc (Tower.ZFStackBase._∈_ base) x)
        → Inner.WF.C.BaseWFClosure
      wfClosure = Inner.wfClosure

      module WithFO
        (FOW : FO.StagedFOWitnesses)
        (wfMem : (x : Tower.ZFStackBase.SetU base) → WFd.Acc (Tower.ZFStackBase._∈_ base) x)
        where

        module Lifted = Inner.WithFO (FO.foWitnesses FOW) wfMem

        open Lifted public
