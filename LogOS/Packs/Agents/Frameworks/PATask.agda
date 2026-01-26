{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.PATask where

open import LogOS.Prelude

import LogOS.Packs.Agents.Frameworks.Core as Core
import LogOS.Packs.Agents.Frameworks.UniversalIR as U
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Domain.UniversalIR.Schemes as US
import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
import LogOS.Domain.UniversalIR.Languages.Lambda as Lambda
import LogOS.Domain.UniversalIR.Languages.Ethereum as Ethereum
import LogOS.Domain.UniversalIR.Languages.QuantumOracle as QuantumOracle
import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as QuantumCircuit

-- Concrete PATask frameworks: each is a Choice into the shared UProcess.

minskyFramework : Core.Framework U.PATask ℕ U.UProcess
minskyFramework = record { choice = U.minskyChoice }

lambdaFramework : Core.Framework U.PATask ℕ U.UProcess
lambdaFramework = record { choice = U.lambdaChoice }

ethereumFramework : Core.Framework U.PATask ℕ U.UProcess
ethereumFramework = record { choice = U.ethereumChoice }

oracleFramework : Core.Framework U.PATask ℕ U.UProcess
oracleFramework = record { choice = U.oracleChoice }

quantumCircuitFramework : Core.Framework U.PATask ℕ U.UProcess
quantumCircuitFramework = record { choice = U.quantumCircuitChoice }

-- --------------------------------------------------------------------------
-- Budgeted PATask frameworks
-- --------------------------------------------------------------------------

-- Use the shared bounded-task type from the UniversalIR scheme layer.
open US using (Bounded; steps; input; mkChoice)

boundedMinskyChoice : Cat.Choice (Bounded U.PATask) U.UProcess
boundedMinskyChoice =
  mkChoice U.UProcess
    (λ bt → Minsky.compile (input bt))
    steps

boundedLambdaChoice : Cat.Choice (Bounded U.PATask) U.UProcess
boundedLambdaChoice =
  mkChoice U.UProcess
    (λ bt → Lambda.compile (input bt))
    steps

boundedEthereumChoice : Cat.Choice (Bounded U.PATask) U.UProcess
boundedEthereumChoice =
  mkChoice U.UProcess
    (λ bt → Ethereum.compile (input bt))
    steps

boundedOracleChoice : Cat.Choice (Bounded U.PATask) U.UProcess
boundedOracleChoice =
  mkChoice U.UProcess
    (λ bt → QuantumOracle.compile (input bt))
    steps

boundedQuantumCircuitChoice : Cat.Choice (Bounded U.PATask) U.UProcess
boundedQuantumCircuitChoice =
  mkChoice U.UProcess
    (λ bt → QuantumCircuit.compile (input bt))
    steps

boundedMinskyFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedMinskyFramework = record { choice = boundedMinskyChoice }

boundedLambdaFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedLambdaFramework = record { choice = boundedLambdaChoice }

boundedEthereumFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedEthereumFramework = record { choice = boundedEthereumChoice }

boundedOracleFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedOracleFramework = record { choice = boundedOracleChoice }

boundedQuantumCircuitFramework : Core.Framework (Bounded U.PATask) ℕ U.UProcess
boundedQuantumCircuitFramework = record { choice = boundedQuantumCircuitChoice }
