{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Task where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

record MeasuredTask (Payload : Set) (measurePayload : Payload → ℕ) : Set where
  constructor mkMeasuredTask
  field
    payload : Payload

open MeasuredTask public using (payload)

measureTask
  : ∀ {Payload : Set} {measurePayload : Payload → ℕ}
  → MeasuredTask Payload measurePayload
  → ℕ
measureTask {measurePayload = measurePayload} sourceTask =
  measurePayload (payload sourceTask)

-- Primitive arithmetic operation fragment.
data ArithmeticTask : Set where
  add : ArithmeticTask
  multiply : ArithmeticTask

record ArithmeticPayload : Set where
  constructor mkArithmeticPayload
  field
    selectedOperation : ArithmeticTask
    leftOperand : ℕ
    rightOperand : ℕ

arithmeticFuel : ArithmeticPayload → ℕ
arithmeticFuel sourceTask with ArithmeticPayload.selectedOperation sourceTask
... | add =
  ArithmeticPayload.leftOperand sourceTask + ArithmeticPayload.rightOperand sourceTask
... | multiply =
  ArithmeticPayload.leftOperand sourceTask * ArithmeticPayload.rightOperand sourceTask

PATask : Set
PATask = MeasuredTask ArithmeticPayload arithmeticFuel

operation : PATask → ArithmeticTask
operation sourceTask = ArithmeticPayload.selectedOperation (payload sourceTask)

operandOne : PATask → ℕ
operandOne sourceTask = ArithmeticPayload.leftOperand (payload sourceTask)

operandTwo : PATask → ℕ
operandTwo sourceTask = ArithmeticPayload.rightOperand (payload sourceTask)

mkPATask : ArithmeticTask → ℕ → ℕ → PATask
mkPATask selectedOperation leftOperand rightOperand =
  mkMeasuredTask (mkArithmeticPayload selectedOperation leftOperand rightOperand)

taskFuel : PATask → ℕ
taskFuel = measureTask

addTask : ℕ → ℕ → PATask
addTask leftOperand rightOperand = mkPATask add leftOperand rightOperand

multiplyTask : ℕ → ℕ → PATask
multiplyTask leftOperand rightOperand = mkPATask multiply leftOperand rightOperand

evaluate : PATask → ℕ
evaluate = taskFuel

-- ============================================================================
-- A wider, still complete task fragment: arithmetic expressions.
-- This remains intentionally minimal but allows a richer shape than binary pairs.
-- ============================================================================

infixl 6 _+E_
infixl 7 _*E_

data PAExpr : Set where
  var : ℕ → PAExpr
  lit : ℕ → PAExpr
  _+E_ : PAExpr → PAExpr → PAExpr
  _*E_ : PAExpr → PAExpr → PAExpr

lookupDefaultNat : ℕ → List ℕ → ℕ → ℕ
lookupDefaultNat defaultValue [] _ = defaultValue
lookupDefaultNat defaultValue (value ∷ _) zero = value
lookupDefaultNat defaultValue (_ ∷ remaining) (suc index) = lookupDefaultNat defaultValue remaining index

evalExpression : PAExpr → List ℕ → ℕ
evalExpression (var index) environment = lookupDefaultNat 0 environment index
evalExpression (lit value) _ = value
evalExpression (leftExpr +E rightExpr) environment =
  evalExpression leftExpr environment + evalExpression rightExpr environment
evalExpression (leftExpr *E rightExpr) environment =
  evalExpression leftExpr environment * evalExpression rightExpr environment

record ExpressionPayload : Set where
  constructor mkExpressionPayload
  field
    sourceExpression : PAExpr
    sourceEnvironment : List ℕ

expressionFuel : ExpressionPayload → ℕ
expressionFuel sourceTask =
  evalExpression
    (ExpressionPayload.sourceExpression sourceTask)
    (ExpressionPayload.sourceEnvironment sourceTask)

PAExprTask : Set
PAExprTask = MeasuredTask ExpressionPayload expressionFuel

expression : PAExprTask → PAExpr
expression sourceTask = ExpressionPayload.sourceExpression (payload sourceTask)

environment : PAExprTask → List ℕ
environment sourceTask = ExpressionPayload.sourceEnvironment (payload sourceTask)

mkPAExprTask : PAExpr → List ℕ → PAExprTask
mkPAExprTask sourceExpression sourceEnvironment =
  mkMeasuredTask (mkExpressionPayload sourceExpression sourceEnvironment)

evaluateExpressionTask : PAExprTask → ℕ
evaluateExpressionTask = measureTask
