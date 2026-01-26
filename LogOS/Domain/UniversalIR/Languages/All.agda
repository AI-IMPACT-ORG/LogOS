{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Languages.All where

import LogOS.Domain.UniversalIR.Languages.Minsky as Minskyₜ
import LogOS.Domain.UniversalIR.Languages.Ethereum as Ethereumₜ
import LogOS.Domain.UniversalIR.Languages.Lambda as Lambdaₜ
import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as QuantumCircuitₜ
import LogOS.Domain.UniversalIR.Languages.QuantumOracle as QuantumOracleₜ

module Minsky = Minskyₜ
module Ethereum = Ethereumₜ
module Lambda = Lambdaₜ
module QuantumCircuit = QuantumCircuitₜ
module QuantumOracle = QuantumOracleₜ

