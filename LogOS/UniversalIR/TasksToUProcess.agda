{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.TasksToUProcess where

-- Convenience wrappers: transport “raw code tasks” along the canonical process
-- morphisms into the universal semantic center (`UProcess`).
--
-- This packages up the generic results from `LogOS.Computation.Tasks` for each
-- UniversalIR backend (Minsky, Lambda, EVM, quantum oracle/circuit).

open import LogOS.Prelude

open import LogOS.Computation.Tasks
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Minimal.ScaleOps using (ScaleOps)
import LogOS.Minimal.Truth as Truth
open import LogOS.UniversalIR.Core using (UCode)
import LogOS.UniversalIR.Schemes as U

module ForObservation {ℓO : Level} {Obs : Set ℓO} (obs : UCode → Obs) where

  UProcess : Cat.Process {ℓO} {lzero} {lzero} Obs
  UProcess = U.UProcessAt obs

  module TU = ForProcess UProcess

  module From
    {ℓC : Level}
    (P : Cat.Process {ℓO} {ℓC} {lzero} Obs)
    (hc : Cat.ProcessHomCost P UProcess)
    where

    module TP = ForProcess P

    private
      maph : Cat.Process.Con P → Cat.Process.Con UProcess
      maph = Cat.ProcessHom.map (Cat.ProcessHomCost.hom hc)

    toUCodeTask : TP.CodeTask → TU.CodeTask
    toUCodeTask = mapFuelled maph

    runTask→U : ∀ t → TU.runTask (toUCodeTask t) ≡ TP.runTask t
    runTask→U =
      let
        module TC = TP.TransportCost hc
      in
      TC.runTask-map

    toUGradeTask : TP.GradeTask → TU.GradeTask
    toUGradeTask t =
      mkGraded
        (Truth.GuardedCore.GradeHom.map (Cat.ProcessHomCost.grade hc) (Graded.grade t))
        (maph (Graded.payload t))

    run≤Task→U
      : ∀ (OpsP : ScaleOps (Cat.Process.Q P))
          (OpsU : ScaleOps (Cat.Process.Q UProcess))
          t
      → (stepsEq :
           ScaleOps.steps OpsU
             (ScaleOps.budget OpsU (Truth.GuardedCore.GradeHom.map (Cat.ProcessHomCost.grade hc) (Graded.grade t)))
           ≡
           ScaleOps.steps OpsP (ScaleOps.budget OpsP (Graded.grade t)))
      → TU.run≤Task OpsU (toUGradeTask t) ≡ TP.run≤Task OpsP t
    run≤Task→U OpsP OpsU t stepsEq =
      let
        module TC = TP.TransportCost hc
      in
      TC.run≤Task-map OpsP OpsU t stepsEq

  module Minsky  = From (U.MinskyProcessAt  obs) (U.Minsky→UCostAt  obs)
  module Ethereum = From (U.EthereumProcessAt obs) (U.Ethereum→UCostAt obs)
  module Lambda  = From (U.LambdaProcessAt  obs) (U.Lambda→UCostAt  obs)
  module Oracle  = From (U.QuantumOracleProcessAt obs) (U.Oracle→UCostAt obs)
  module Circuit = From (U.QuantumCircuitProcessAt obs) (U.Circuit→UCostAt obs)

-- Default ℕ-center (canonical observation).
module Default = ForObservation U.observeU
