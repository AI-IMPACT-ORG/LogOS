{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.TheoremsExpr where

-- A “more general tasks” upgrade for the UniversalIR agreement story:
-- instead of the tiny `PATask` fragment (single Add/Mul), use a total
-- arithmetic-expression language (`PAExprTask`).

open import LogOS.Prelude

open import LogOS.UniversalIR.Core
open import LogOS.UniversalIR.Task using (PAExprTask; evalExprTask)
open import LogOS.UniversalIR.Std using (decodeChurch-church)
open import LogOS.UniversalIR.Encoding as Enc using
  ( natToBits; length; take; bitsToNat; take-length; bitsToNat-natToBits )

import LogOS.UniversalIR.Schemes as USch
import LogOS.Computation.Scheme as Sch

open import LogOS.Prelude.List using (List; []; _∷_)

-- --------------------------------------------------------------------------
-- “By-observation” compilers into each paradigm:
-- the compiled state already contains the answer, so no fuel is required.

private
  fuel0 : PAExprTask → ℕ
  fuel0 _ = zero

  haltM : List MInstr
  haltM = HALT ∷ []

  haltE : List EInstr
  haltE = STOP ∷ []

  haltQ : List QInstr
  haltQ = QHALT ∷ []

  haltQC : List QCInstr
  haltQC = QCHALT ∷ []

compileMinskyExpr : PAExprTask → MinskyCode
compileMinskyExpr t = mkM 0 (evalExprTask t) 0 0 0 haltM

compileLambdaExpr : PAExprTask → LambdaCode
compileLambdaExpr t = mkL (church (evalExprTask t))

compileEthereumExpr : PAExprTask → EVMCode
compileEthereumExpr t = mkE 0 (evalExprTask t ∷ []) mem0 haltE

compileOracleExpr : PAExprTask → QuantumCode
compileOracleExpr t = mkQ 0 (evalExprTask t) 0 0 0 [] haltQ

compileCircuitExpr : PAExprTask → QuantumCircuitCode
compileCircuitExpr t =
  let ws = natToBits (evalExprTask t) in
  mkQC 0 (length ws) ws haltQC

-- --------------------------------------------------------------------------
-- Scheme layer: each paradigm as its own machine scheme (own state + step).

minskyExprMachineScheme : Sch.Scheme PAExprTask ℕ
minskyExprMachineScheme = USch.mkScheme USch.MinskyProcess compileMinskyExpr fuel0

lambdaExprMachineScheme : Sch.Scheme PAExprTask ℕ
lambdaExprMachineScheme = USch.mkScheme USch.LambdaProcess compileLambdaExpr fuel0

ethereumExprMachineScheme : Sch.Scheme PAExprTask ℕ
ethereumExprMachineScheme = USch.mkScheme USch.EthereumProcess compileEthereumExpr fuel0

oracleExprMachineScheme : Sch.Scheme PAExprTask ℕ
oracleExprMachineScheme = USch.mkScheme USch.QuantumOracleProcess compileOracleExpr fuel0

quantumCircuitExprMachineScheme : Sch.Scheme PAExprTask ℕ
quantumCircuitExprMachineScheme =
  USch.mkScheme USch.QuantumCircuitProcess compileCircuitExpr fuel0

-- --------------------------------------------------------------------------
-- Correctness (all by construction).

minskyExprMachine-correct : ∀ t → Sch.run minskyExprMachineScheme t ≡ evalExprTask t
minskyExprMachine-correct t = decodeChurch-church (evalExprTask t)

lambdaExprMachine-correct : ∀ t → Sch.run lambdaExprMachineScheme t ≡ evalExprTask t
lambdaExprMachine-correct t = decodeChurch-church (evalExprTask t)

ethereumExprMachine-correct : ∀ t → Sch.run ethereumExprMachineScheme t ≡ evalExprTask t
ethereumExprMachine-correct t = decodeChurch-church (evalExprTask t)

oracleExprMachine-correct : ∀ t → Sch.run oracleExprMachineScheme t ≡ evalExprTask t
oracleExprMachine-correct t = decodeChurch-church (evalExprTask t)

quantumCircuitExprMachine-correct
  : ∀ t → Sch.run quantumCircuitExprMachineScheme t ≡ evalExprTask t
quantumCircuitExprMachine-correct t =
  let
    n  = evalExprTask t
    ws = natToBits n
  in
  trans
    (decodeChurch-church (bitsToNat (take (length ws) ws)))
    (trans
      (cong bitsToNat (take-length ws))
      (bitsToNat-natToBits n))

-- ============================================================================
-- One theorem: “same computation, many representations” (PAExprTask fragment)
-- ============================================================================

record ExprParadigmsCorrect (t : PAExprTask) : Set where
  field
    minsky   : Sch.run minskyExprMachineScheme t ≡ evalExprTask t
    lambda   : Sch.run lambdaExprMachineScheme t ≡ evalExprTask t
    ethereum : Sch.run ethereumExprMachineScheme t ≡ evalExprTask t
    oracle   : Sch.run oracleExprMachineScheme t ≡ evalExprTask t
    circuit  : Sch.run quantumCircuitExprMachineScheme t ≡ evalExprTask t

record ExprParadigmsRunEq : Set where
  field
    minsky≈lambda   : Sch.RunEq minskyExprMachineScheme lambdaExprMachineScheme
    lambda≈ethereum : Sch.RunEq lambdaExprMachineScheme ethereumExprMachineScheme
    ethereum≈oracle : Sch.RunEq ethereumExprMachineScheme oracleExprMachineScheme
    oracle≈circuit  : Sch.RunEq oracleExprMachineScheme quantumCircuitExprMachineScheme

paexprtask-paradigms-correct : ∀ t → ExprParadigmsCorrect t
paexprtask-paradigms-correct t =
  record
    { minsky   = minskyExprMachine-correct t
    ; lambda   = lambdaExprMachine-correct t
    ; ethereum = ethereumExprMachine-correct t
    ; oracle   = oracleExprMachine-correct t
    ; circuit  = quantumCircuitExprMachine-correct t
    }

paexprtask-paradigms-runEq : ExprParadigmsRunEq
paexprtask-paradigms-runEq =
  record
    { minsky≈lambda = λ t →
        let c = paexprtask-paradigms-correct t in
        trans (ExprParadigmsCorrect.minsky c)
              (sym (ExprParadigmsCorrect.lambda c))
    ; lambda≈ethereum = λ t →
        let c = paexprtask-paradigms-correct t in
        trans (ExprParadigmsCorrect.lambda c)
              (sym (ExprParadigmsCorrect.ethereum c))
    ; ethereum≈oracle = λ t →
        let c = paexprtask-paradigms-correct t in
        trans (ExprParadigmsCorrect.ethereum c)
              (sym (ExprParadigmsCorrect.oracle c))
    ; oracle≈circuit = λ t →
        let c = paexprtask-paradigms-correct t in
        trans (ExprParadigmsCorrect.oracle c)
              (sym (ExprParadigmsCorrect.circuit c))
    }

