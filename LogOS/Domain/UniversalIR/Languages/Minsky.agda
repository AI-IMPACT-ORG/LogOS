{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Languages.Minsky where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Task using (PATask; Add; Mul)
open import LogOS.Domain.UniversalIR.Backend using (Backend; mkBackend)
open import LogOS.Domain.UniversalIR.Core
open import LogOS.Prelude.List using (List; []; _∷_)

-- Compile a PA task to a 4-register Minsky machine state.
--
-- This file gives a concrete “Minsky instance” (programs + fuel bounds) that
-- is used as a reference point for other backends. The scheme-centric view
-- (“machines as schemes”) packages this as `minskyMachineScheme` in
-- `LogOS.Domain.UniversalIR.Schemes`.
-- We compile addition by looping on `r1`:
--   while r1 > 0: r1--; r0++; halt.

progAdd : List MInstr
progAdd =
  DECJZ R1 1 2 ∷
  INC R0 0 ∷
  HALT ∷
  []

-- Multiplication using 4 registers:
--   r0 := 0            (accumulator)
--   r1 := a            (outer counter)
--   r2 := b            (multiplicand)
--   r3 := 0            (temp for restoring r2)
--
-- Loop: while r1>0 { r1--; r0 += r2 (preserving r2) } ; halt

progMul : List MInstr
progMul =
  DECJZ R1 1 6 ∷        -- outer: dec r1; if zero halt
  DECJZ R2 2 4 ∷        -- inner: move r2 to r3 while incrementing r0
  INC R0 3 ∷
  INC R3 1 ∷
  DECJZ R3 5 0 ∷        -- restore r2 from r3, then loop
  INC R2 4 ∷
  HALT ∷
  []

compileBrand : PATask → MinskyCode
compileBrand t with PATask.op t
... | Add = mkM 0 (PATask.a t) (PATask.b t) 0 0 progAdd
... | Mul = mkM 0 0 (PATask.a t) (PATask.b t) 0 progMul

fuelInnerMul : ℕ → ℕ
fuelInnerMul zero    = suc zero
fuelInnerMul (suc b) = suc (suc (suc (fuelInnerMul b)))  -- +3 (DECJZ; INC; INC)

fuelRestoreMul : ℕ → ℕ
fuelRestoreMul zero    = suc zero
fuelRestoreMul (suc b) = suc (suc (fuelRestoreMul b))     -- +2 (DECJZ; INC)

perIterMul : ℕ → ℕ
perIterMul b = suc (fuelInnerMul b + fuelRestoreMul b)    -- +1 outer DECJZ

fuelMul : ℕ → ℕ → ℕ
fuelMul zero    _ = suc zero
fuelMul (suc a) b = perIterMul b + fuelMul a b

backend : Backend PATask MinskyCode
backend = mkBackend compileBrand UM

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
