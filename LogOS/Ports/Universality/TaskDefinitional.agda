{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.TaskDefinitional where

-- Definitional/bookkeeping equalities for the minimal task fragment.

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc; _+_; _*_)
open import LogOS.Prelude.List using ([]; _∷_)
import LogOS.Ports.Universality.Task as Task

taskFuel-add
  : ∀ leftOperand rightOperand
  → Task.taskFuel (Task.addTask leftOperand rightOperand)
      ≡ leftOperand + rightOperand
taskFuel-add _ _ = refl

taskFuel-multiply
  : ∀ leftOperand rightOperand
  → Task.taskFuel (Task.multiplyTask leftOperand rightOperand)
      ≡ leftOperand * rightOperand
taskFuel-multiply _ _ = refl

evaluate≡taskFuel
  : ∀ sourceTask
  → Task.evaluate sourceTask ≡ Task.taskFuel sourceTask
evaluate≡taskFuel _ = refl

lookupDefaultNat-empty
  : ∀ defaultValue index
  → Task.lookupDefaultNat defaultValue [] index ≡ defaultValue
lookupDefaultNat-empty _ _ = refl

lookupDefaultNat-zero
  : ∀ defaultValue value remaining
  → Task.lookupDefaultNat defaultValue (value ∷ remaining) zero ≡ value
lookupDefaultNat-zero _ _ _ = refl

lookupDefaultNat-suc
  : ∀ defaultValue value remaining index
  → Task.lookupDefaultNat defaultValue (value ∷ remaining) (suc index)
      ≡ Task.lookupDefaultNat defaultValue remaining index
lookupDefaultNat-suc _ _ _ _ = refl

evalExpression-var
  : ∀ index environment
  → Task.evalExpression (Task.var index) environment
      ≡ Task.lookupDefaultNat 0 environment index
evalExpression-var _ _ = refl

evalExpression-lit
  : ∀ value environment
  → Task.evalExpression (Task.lit value) environment ≡ value
evalExpression-lit _ _ = refl

evalExpression-+E
  : ∀ leftExpr rightExpr environment
  → Task.evalExpression (leftExpr Task.+E rightExpr) environment
      ≡ Task.evalExpression leftExpr environment
      + Task.evalExpression rightExpr environment
evalExpression-+E _ _ _ = refl

evalExpression-*E
  : ∀ leftExpr rightExpr environment
  → Task.evalExpression (leftExpr Task.*E rightExpr) environment
      ≡ Task.evalExpression leftExpr environment
      * Task.evalExpression rightExpr environment
evalExpression-*E _ _ _ = refl

evaluateExpressionTask-mk
  : ∀ expression environment
  → Task.evaluateExpressionTask (Task.mkPAExprTask expression environment)
      ≡ Task.evalExpression expression environment
evaluateExpressionTask-mk _ _ = refl

evaluateExpressionTask-evalExpression
  : ∀ sourceTask
  → Task.evaluateExpressionTask sourceTask
      ≡ Task.evalExpression
          (Task.expression sourceTask)
          (Task.environment sourceTask)
evaluateExpressionTask-evalExpression _ = refl
