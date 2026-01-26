{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.ArbitraryTasks where

-- Worked example: “arbitrary tasks” commute along UniversalIR process morphisms.
--
-- This demonstrates the generic task invariance lemmas from `LogOS.Computation.Tasks`
-- in the concrete UniversalIR setting: Minsky is a presentation that factors
-- through the universal semantic center (`UProcess`).

open import LogOS.Prelude

open import LogOS.Computation.Tasks
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Domain.UniversalIR.Schemes as U

module TM = ForProcess U.MinskyProcess
module TU = ForProcess U.UProcess

private
  hc : Cat.ProcessHomCost U.MinskyProcess U.UProcess
  hc = U.Minsky→UCost

  maph : Cat.Process.Con U.MinskyProcess → Cat.Process.Con U.UProcess
  maph = Cat.ProcessHom.map (Cat.ProcessHomCost.hom hc)

toUCodeTask : TM.CodeTask → TU.CodeTask
toUCodeTask = mapFuelled maph

runTask-minsky→U
  : ∀ t → TU.runTask (toUCodeTask t) ≡ TM.runTask t
runTask-minsky→U =
  let
    module TC = TM.TransportCost hc
  in
  TC.runTask-map

toUGradeTask : TM.GradeTask → TU.GradeTask
toUGradeTask t =
  mkGraded
    (Cat.castScale→ hc (Graded.grade t))
    (maph (Graded.payload t))

run≤Task-minsky→U
  : ∀ Ops t
  → TU.run≤Task (Cat.castOps→ hc Ops) (toUGradeTask t)
    ≡ TM.run≤Task Ops t
run≤Task-minsky→U Ops t =
  let
    module TC = TM.TransportCost hc
  in
  TC.run≤Task-map Ops t
