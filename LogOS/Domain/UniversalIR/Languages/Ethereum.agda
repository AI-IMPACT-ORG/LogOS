{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Languages.Ethereum where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Task using (PATask; Add; Mul)
open import LogOS.Domain.UniversalIR.Backend using (Backend; mkBackend)
open import LogOS.Domain.UniversalIR.Core

open import Data.List using (List; []; _∷_)

-- EVM-like backend (stack machine). We compile addition as:
--
-- This file exposes a minimal step-budgeted `run`; the main universality interface
-- uses the corresponding `Scheme` in `LogOS.Domain.UniversalIR.Schemes`.
--   PUSH b; PUSH a; ADD; STOP

compileBrand : PATask → EVMCode
compileBrand t with PATask.op t
... | Add =
  mkE 0 [] mem0
    (PUSH (PATask.b t) ∷ PUSH (PATask.a t) ∷ ADD ∷ STOP ∷ [])
... | Mul =
  mkE 0 [] mem0
    (PUSH (PATask.b t) ∷ PUSH (PATask.a t) ∷ MUL ∷ STOP ∷ [])

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
