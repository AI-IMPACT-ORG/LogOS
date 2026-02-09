{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.PATask where

open import LogOS.Prelude

import LogOS.Packs.Agents.Frameworks.Core as Core
import LogOS.Packs.Agents.Frameworks.UniversalIR as U
import LogOS.Computation.SchemeCategory as Cat
import LogOS.UniversalIR.Schemes as US
import LogOS.UniversalIR.Languages.Minsky as Minsky
import LogOS.UniversalIR.Languages.Lambda as Lambda
import LogOS.UniversalIR.Languages.Ethereum as Ethereum
import LogOS.UniversalIR.Languages.QuantumOracle as QuantumOracle
import LogOS.UniversalIR.Languages.QuantumCircuit as QuantumCircuit

-- Concrete PATask frameworks: each is a Choice into the shared UProcess.
-- Concrete PATask frameworks: each is an Interface into the shared UProcess.

minskyFramework : Core.Framework U.PATask ℕ U.UProcess
minskyFramework = record { interface = U.minskyInterface }

lambdaFramework : Core.Framework U.PATask ℕ U.UProcess
lambdaFramework = record { interface = U.lambdaInterface }

ethereumFramework : Core.Framework U.PATask ℕ U.UProcess
ethereumFramework = record { interface = U.ethereumInterface }

oracleFramework : Core.Framework U.PATask ℕ U.UProcess
oracleFramework = record { interface = U.oracleInterface }

quantumCircuitFramework : Core.Framework U.PATask ℕ U.UProcess
quantumCircuitFramework = record { interface = U.quantumCircuitInterface }

-- --------------------------------------------------------------------------
-- Budgeted PATask frameworks
-- --------------------------------------------------------------------------

-- Use the shared bounded-task type from the UniversalIR scheme layer.
open US using (Bounded; steps; input; mkInterface)

boundedMinskyInterface : Cat.Interface (Bounded U.PATask) U.UProcess
boundedMinskyInterface =
  mkInterface U.UProcess
    (λ bt → Minsky.compile (input bt))
    steps

boundedLambdaInterface : Cat.Interface (Bounded U.PATask) U.UProcess
boundedLambdaInterface =
  mkInterface U.UProcess
    (λ bt → Lambda.compile (input bt))
    steps

boundedEthereumInterface : Cat.Interface (Bounded U.PATask) U.UProcess
boundedEthereumInterface =
  mkInterface U.UProcess
    (λ bt → Ethereum.compile (input bt))
    steps

boundedOracleInterface : Cat.Interface (Bounded U.PATask) U.UProcess
boundedOracleInterface =
  mkInterface U.UProcess
    (λ bt → QuantumOracle.compile (input bt))
    steps

boundedQuantumCircuitInterface : Cat.Interface (Bounded U.PATask) U.UProcess
boundedQuantumCircuitInterface =
  mkInterface U.UProcess
    (λ bt → QuantumCircuit.compile (input bt))
    steps

boundedMinskyFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedMinskyFramework = record { interface = boundedMinskyInterface }

boundedLambdaFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedLambdaFramework = record { interface = boundedLambdaInterface }

boundedEthereumFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedEthereumFramework = record { interface = boundedEthereumInterface }

boundedOracleFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedOracleFramework = record { interface = boundedOracleInterface }

boundedQuantumCircuitFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedQuantumCircuitFramework = record { interface = boundedQuantumCircuitInterface }
