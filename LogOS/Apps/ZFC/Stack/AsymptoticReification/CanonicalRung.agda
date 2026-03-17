{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung where

-- Canonical same-stage rung data for ZFC-style late collapse.
--
-- This module contains only the data determined once a stage-local
-- reification/collapse/base package is fixed. Realised same-stage semantics live
-- in `CompletionSemantics`, parameterised by an explicit completion witness.

open import LogOS.Prelude
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility using
  ( StagedPredicateReification )

import LogOS.Apps.ZFC.Stack.AsymptoticReification.LateCollapseTower as LCT
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as PTower
import LogOS.Apps.ZFC.Stack.WellFounded as WFd
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

record CanonicalRung {ℓ : Level} (C : ZF.SetContext {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    staged : StagedPredicateReification C

  module Tower = LCT.ForStaged C staged

  field
    collapse : Tower.FlowCollapse
    baseAssumptions : Tower.BaseAssumptions

  module Closed = Tower.WithFlowCollapse collapse
  module Base = Closed.ForBase baseAssumptions

  base : PTower.ZFStackBase {ℓ}
  base = Base.base

  FOWitnesses : Set (lsuc (lsuc ℓ))
  FOWitnesses = Base.FO.StagedFOWitnesses

  StructuralAssumptions : Set (lsuc (lsuc ℓ))
  StructuralAssumptions = Base.StructuralAssumptions

  WFMem : Set ℓ
  WFMem = (x : PTower.ZFStackBase.SetU base) -> WFd.Acc (PTower.ZFStackBase._∈_ base) x

  module Complete (FOW : FOWitnesses) (wfMem : WFMem) where
    module Impl = Base.WithFO FOW wfMem

    reifiedZFCFO = Impl.reifiedZFCFO
    baseᵂ = Impl.baseᵂ
    stackFO₋Fnd = Impl.stackFO₋Fnd
    stackFO = Impl.stackFO
    proofModel = Impl.proofModel

open CanonicalRung public
