{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CumulativeHierarchyTower where

-- Reusable two-rung cumulative hierarchy packaging:
-- - one same-stage late-collapse tower at the current stage,
-- - one same-stage late-collapse tower at the successor stage,
-- - one cross-stage bridge reifying current-stage predicates in the larger
--   successor carrier.
--
-- This keeps the staged ladder explicit without pretending that the cross-stage
-- bridge alone already yields a same-stage model at the successor level.

open import LogOS.Prelude
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility using
  ( StagedPredicateReification )
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageReificationPort using
  ( CrossStagePredicateReification )

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageFOFromReification as CSFO
import LogOS.Apps.ZFC.Stack.AsymptoticReification.LateCollapseTower as LCT
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.WellFounded as WFd
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

module For
  {ℓ₀ ℓ₁ : Level}
  (C₀ : ZF.SetContext {ℓ₀})
  (S₀ : StagedPredicateReification C₀)
  (C₁ : ZF.SetContext {ℓ₁})
  (S₁ : StagedPredicateReification C₁)
  (R↑ : CrossStagePredicateReification C₀ C₁)
  where

  module Lower = LCT.ForStaged C₀ S₀
  module Upper = LCT.ForStaged C₁ S₁

  LowerFlowCollapse : Set (lsuc ℓ₀)
  LowerFlowCollapse = Lower.FlowCollapse

  UpperFlowCollapse : Set (lsuc ℓ₁)
  UpperFlowCollapse = Upper.FlowCollapse

  LowerBaseAssumptions : Set (lsuc (lsuc ℓ₀))
  LowerBaseAssumptions = Lower.BaseAssumptions

  UpperBaseAssumptions : Set (lsuc (lsuc ℓ₁))
  UpperBaseAssumptions = Upper.BaseAssumptions

  module WithFlowCollapse
    (close₀ : LowerFlowCollapse)
    (close₁ : UpperFlowCollapse)
    where

    module LowerClosed = Lower.WithFlowCollapse close₀
    module UpperClosed = Upper.WithFlowCollapse close₁

    module ForBase
      (B₀ : LowerBaseAssumptions)
      (B₁ : UpperBaseAssumptions)
      where

      module LowerBase = LowerClosed.ForBase B₀
      module UpperBase = UpperClosed.ForBase B₁
      module Cross = CSFO.CrossStageFO LowerBase.base C₁ R↑

      lowerBase : Tower.ZFStackBase {ℓ₀}
      lowerBase = LowerBase.base

      upperBase : Tower.ZFStackBase {ℓ₁}
      upperBase = UpperBase.base

      LowerStructuralAssumptions : Set (lsuc (lsuc ℓ₀))
      LowerStructuralAssumptions = LowerBase.StructuralAssumptions

      UpperStructuralAssumptions : Set (lsuc (lsuc ℓ₁))
      UpperStructuralAssumptions = UpperBase.StructuralAssumptions

      lowerWFClosure
        : ((x : Tower.ZFStackBase.SetU lowerBase) → WFd.Acc (Tower.ZFStackBase._∈_ lowerBase) x)
        → LowerBase.WF.C.BaseWFClosure
      lowerWFClosure = LowerBase.wfClosure

      upperWFClosure
        : ((x : Tower.ZFStackBase.SetU upperBase) → WFd.Acc (Tower.ZFStackBase._∈_ upperBase) x)
        → UpperBase.WF.C.BaseWFClosure
      upperWFClosure = UpperBase.wfClosure

      module WithLowerFO
        (FOW₀ : LowerBase.FO.StagedFOWitnesses)
        (wfMem₀ : (x : Tower.ZFStackBase.SetU lowerBase) → WFd.Acc (Tower.ZFStackBase._∈_ lowerBase) x)
        where

        module Impl = LowerBase.WithFO FOW₀ wfMem₀
        open Impl public

      module WithUpperFO
        (FOW₁ : UpperBase.FO.StagedFOWitnesses)
        (wfMem₁ : (x : Tower.ZFStackBase.SetU upperBase) → WFd.Acc (Tower.ZFStackBase._∈_ upperBase) x)
        where

        module Impl = UpperBase.WithFO FOW₁ wfMem₁
        open Impl public
