{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Languages.Ethereum where

open import LogOS.Prelude
open import LogOS.UniversalIR.Task using (PATask; Add; Mul)
open import LogOS.UniversalIR.Backend using (Backend; mkBackend)
open import LogOS.UniversalIR.Core

open import LogOS.Prelude.List using (List; []; _∷_)
import LogOS.UniversalIR.Core.Ethereum as CoreE

-- EVM-like backend (stack machine). We compile addition as:
--
-- This file exposes a minimal step-budgeted `run`; the main universality interface
-- uses the corresponding `Scheme` in `LogOS.UniversalIR.Schemes`.
--   PUSH b; PUSH a; ADD; STOP

compileProg : PATask → CoreE.EVMProg
compileProg t with PATask.op t
... | Add = CoreE.mkProg (PUSH (PATask.b t) ∷ PUSH (PATask.a t) ∷ ADD ∷ STOP ∷ [])
... | Mul = CoreE.mkProg (PUSH (PATask.b t) ∷ PUSH (PATask.a t) ∷ MUL ∷ STOP ∷ [])

compileState : PATask → CoreE.EVMState
compileState _ = CoreE.mkState 0 [] mem0

compileBrand : PATask → EVMCode
compileBrand t = CoreE.mkCode (compileState t) (compileProg t)

backend : Backend PATask EVMCode
backend = mkBackend compileBrand UE

compile : PATask → UCode
compile t = Backend.toUCode backend t

fuel : PATask → ℕ
fuel _ = suc (suc (suc zero)) -- PUSH; PUSH; (ADD/MUL)

exec : ℕ → PATask → UCode
exec n t = Backend.exec backend n t

toIR : PATask → UCode
toIR t = Backend.toIRAt backend (fuel t) t

run : PATask → ℕ
run t = Backend.decodeAt backend (fuel t) t
