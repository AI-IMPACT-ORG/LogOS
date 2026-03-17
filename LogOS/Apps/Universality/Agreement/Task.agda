{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Agreement.Task where

open import LogOS.Prelude

import LogOS.Ports.Universality.Task as Task

import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Adapters.Universality.Lambda as Lambda
import LogOS.Adapters.Universality.EVM as EVM
import LogOS.Adapters.Universality.PreQuantum as PreQuantum
import LogOS.Adapters.Universality.PreQuantumCircuit as PreQuantumCircuit

import LogOS.Apps.Universality.Agreement.Universal as Universal

taskEncodings : Universal.MeasuredEncodings Task.PATask Task.taskFuel
taskEncodings =
  Universal.mkMeasuredEncodings
    (Universal.mkMeasuredEncoding Minsky.minskyFromPATask Minsky.minskyFromPATask-fuel)
    (Universal.mkMeasuredEncoding Lambda.lambdaFromPATask Lambda.lambdaFromPATask-fuel)
    (Universal.mkMeasuredEncoding EVM.evmFromPATask EVM.evmFromPATask-fuel)
    (Universal.mkMeasuredEncoding PreQuantum.preQuantumFromPATask PreQuantum.preQuantumFromPATask-fuel)
    (Universal.mkMeasuredEncoding
      PreQuantumCircuit.preQuantumCircuitFromPATask
      PreQuantumCircuit.preQuantumCircuitFromPATask-fuel)

taskParadigmsAgreement
  : Universal.ParadigmsAgreement Task.PATask Task.taskFuel taskEncodings
taskParadigmsAgreement = Universal.measuredParadigmsAgreement taskEncodings
