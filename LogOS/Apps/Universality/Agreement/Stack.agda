{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Universality.Agreement.Stack where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (_≈_)
import LogOS.LT.Hom as Hom
import LogOS.LT.Stack as LTStack

import LogOS.Ports.Universality.Core as Core
import LogOS.Ports.Universality.Task as Task

import LogOS.Adapters.Universality.Minsky as Minsky

import LogOS.Apps.Universality.Stack as Stack
import LogOS.Apps.Universality.Agreement.Universal as Universal

taskMinskyEncoding : Universal.MeasuredEncoding Task.PATask Task.taskFuel Stack.fromMinsky
taskMinskyEncoding =
  Universal.mkMeasuredEncoding
    Minsky.minskyFromPATask
    Minsky.minskyFromPATask-fuel

exprTaskMinskyEncoding
  : Universal.MeasuredEncoding
      Task.PAExprTask
      Task.evaluateExpressionTask
      Stack.fromMinsky
exprTaskMinskyEncoding =
  Universal.mkMeasuredEncoding
    Minsky.minskyFromPAExprTask
    Minsky.minskyFromPAExprTask-fuel

stackToUniversalObservation : ∀ budgetCode → ∀ stackCode →
  _≈_ Core.universalBoundary
    (Core.universalObservation (Core.runUniversalWithin budgetCode (Hom.mapCode Stack.stackToUniversal stackCode)))
    (Core.universalFuelAfter budgetCode (Core.active (Stack.adapterCodeBoundary (LTStack.opIdx stackCode) (LTStack.code stackCode))))
stackToUniversalObservation budgetCode stackCode =
  Universal.universalFromAdapter
    (LTStack.opIdx stackCode)
    budgetCode
    (LTStack.code stackCode)

stackToTaskObservation : ∀ budgetCode → ∀ sourceTask →
  _≈_ Core.universalBoundary
    (Core.universalObservation
      (Core.runUniversalWithin
        budgetCode
        (Hom.mapCode Stack.stackToUniversal (LTStack.mkStackCode Stack.fromMinsky (Minsky.minskyFromPATask sourceTask)))))
    (Core.universalFuelAfter budgetCode (Core.active (Task.taskFuel sourceTask)))
stackToTaskObservation =
  Universal.measuredObservation
    Stack.fromMinsky
    taskMinskyEncoding

stackToTaskObservationZeroAboveCritical =
  Universal.measuredObservationZeroAboveCritical
    Stack.fromMinsky
    taskMinskyEncoding

stackToPAExprTaskObservation : ∀ budgetCode → ∀ sourceTask →
  _≈_ Core.universalBoundary
    (Core.universalObservation
      (Core.runUniversalWithin
        budgetCode
        (Hom.mapCode Stack.stackToUniversal (LTStack.mkStackCode Stack.fromMinsky (Minsky.minskyFromPAExprTask sourceTask)))))
    (Core.universalFuelAfter budgetCode (Core.active (Task.evaluateExpressionTask sourceTask)))
stackToPAExprTaskObservation =
  Universal.measuredObservation
    Stack.fromMinsky
    exprTaskMinskyEncoding

stackToPAExprTaskObservationZeroAboveCritical =
  Universal.measuredObservationZeroAboveCritical
    Stack.fromMinsky
    exprTaskMinskyEncoding
