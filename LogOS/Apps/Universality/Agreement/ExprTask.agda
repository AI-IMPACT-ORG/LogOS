{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Agreement.ExprTask where

-- The same transport shape for richer expression tasks.

open import LogOS.Prelude

import LogOS.Ports.Universality.Task as Task

import LogOS.Adapters.Universality.Minsky as Minsky
import LogOS.Adapters.Universality.Lambda as Lambda
import LogOS.Adapters.Universality.EVM as EVM
import LogOS.Adapters.Universality.PreQuantum as PreQuantum
import LogOS.Adapters.Universality.PreQuantumCircuit as PreQuantumCircuit

import LogOS.Apps.Universality.Agreement.Universal as Universal

exprTaskEncodings : Universal.MeasuredEncodings Task.PAExprTask Task.evaluateExpressionTask
exprTaskEncodings =
  Universal.mkMeasuredEncodings
    (Universal.mkMeasuredEncoding Minsky.minskyFromPAExprTask Minsky.minskyFromPAExprTask-fuel)
    (Universal.mkMeasuredEncoding Lambda.lambdaFromPAExprTask Lambda.lambdaFromPAExprTask-fuel)
    (Universal.mkMeasuredEncoding EVM.evmFromPAExprTask EVM.evmFromPAExprTask-fuel)
    (Universal.mkMeasuredEncoding PreQuantum.preQuantumFromPAExprTask PreQuantum.preQuantumFromPAExprTask-fuel)
    (Universal.mkMeasuredEncoding
      PreQuantumCircuit.preQuantumCircuitFromPAExprTask
      PreQuantumCircuit.preQuantumCircuitFromPAExprTask-fuel)

exprTaskParadigmsAgreement
  : Universal.ParadigmsAgreement
      Task.PAExprTask
      Task.evaluateExpressionTask
      exprTaskEncodings
exprTaskParadigmsAgreement =
  Universal.measuredParadigmsAgreement exprTaskEncodings
