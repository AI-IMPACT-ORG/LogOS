{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Languages.All where

import LogOS.UniversalIR.Languages.Minsky as Minskyₜ
import LogOS.UniversalIR.Languages.Ethereum as Ethereumₜ
import LogOS.UniversalIR.Languages.Lambda as Lambdaₜ
import LogOS.UniversalIR.Languages.QuantumCircuit as QuantumCircuitₜ
import LogOS.UniversalIR.Languages.QuantumOracle as QuantumOracleₜ

module Minsky = Minskyₜ
module Ethereum = Ethereumₜ
module Lambda = Lambdaₜ
module QuantumCircuit = QuantumCircuitₜ
module QuantumOracle = QuantumOracleₜ

