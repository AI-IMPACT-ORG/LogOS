{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Languages.QuantumOracle where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Task using (PATask; Add; Mul)
open import LogOS.Domain.UniversalIR.Backend using (Backend; mkBackend)
open import LogOS.Domain.UniversalIR.Core

open import Data.List using (List; []; _∷_)

-- “Quantum oracle” backend (classical control + an oracle tape / measurement instruction).
-- This is *not* amplitude-level quantum semantics; for an explicit (basis-state)
-- circuit syntax integrated into UniversalIR, see `LogOS.Domain.UniversalIR.Languages.QuantumCircuit`
-- and the checked example `LogOS.Domain.UniversalIR.Examples.QuantumCircuit`.
--
-- The PA compilers in this file intentionally avoid `MEASURE` (so correctness can
-- be derived from Minsky by erasure). The primitive is present for the cost
-- story; see the Scheme-level example in `LogOS.Domain.UniversalIR.Examples.QuantumOracle`.
-- We compile addition exactly like the Minsky backend, ignoring the oracle:
--   while r1 > 0: r1--; r0++; halt.

progAdd : List QInstr
progAdd =
  QDECJZ R1 1 2 ∷
  QINC R0 0 ∷
  QHALT ∷
  []

progMul : List QInstr
progMul =
  QDECJZ R1 1 6 ∷
  QDECJZ R2 2 4 ∷
  QINC R0 3 ∷
  QINC R3 1 ∷
  QDECJZ R3 5 0 ∷
  QINC R2 4 ∷
  QHALT ∷
  []

compileBrand : PATask → QuantumCode
compileBrand t with PATask.op t
... | Add = mkQ 0 (PATask.a t) (PATask.b t) 0 0 [] progAdd
... | Mul = mkQ 0 0 (PATask.a t) (PATask.b t) 0 [] progMul

fuelInnerMul : ℕ → ℕ
fuelInnerMul zero    = suc zero
fuelInnerMul (suc b) = suc (suc (suc (fuelInnerMul b)))

fuelRestoreMul : ℕ → ℕ
fuelRestoreMul zero    = suc zero
fuelRestoreMul (suc b) = suc (suc (fuelRestoreMul b))

perIterMul : ℕ → ℕ
perIterMul b = suc (fuelInnerMul b + fuelRestoreMul b)

fuelMul : ℕ → ℕ → ℕ
fuelMul zero    _ = suc zero
fuelMul (suc a) b = perIterMul b + fuelMul a b

backend : Backend PATask QuantumCode
backend = mkBackend compileBrand UQ

compile : PATask → UCode
compile t = Backend.toUCode backend t

fuel : PATask → ℕ
fuel t with PATask.op t
... | Add = fuelAddR1 (PATask.b t)
... | Mul = fuelMul (PATask.a t) (PATask.b t)

exec : ℕ → PATask → UCode
exec n t = Backend.exec backend n t

toIR : PATask → UCode
toIR t = Backend.toIRAt backend (fuel t) t

run : PATask → ℕ
run t = Backend.decodeAt backend (fuel t) t
