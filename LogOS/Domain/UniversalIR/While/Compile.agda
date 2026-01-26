{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Compile where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Backend using (Backend; mkBackend)

open import LogOS.Prelude.List using (List; []; _∷_)

-- A concrete non-trivial example task: factorial.
-- The source program is `LogOS.Domain.UniversalIR.While.Language` (see the
-- `While` subfolder), but the
-- compilers below directly emit low-level Minsky/EVM code that implements it.

record FactTask : Set where
  constructor mkFact
  field
    n : ℕ

open FactTask public

-- --------------------------------------------------------------------------
-- Minsky compiler (4-register machine)
--
-- Register convention:
--   R0 = scratch / final output
--   R1 = A (accumulator)
--   R2 = B (counter)
--   R3 = scratch (kept at 0; used for unconditional jumps and mul temp)
--
-- Program layout (pc indices):
--   0..6   : multiplication macro core (like `progMul` but returns to 11)
--   7      : init A := 1
--   8..13  : while B ≠ 0 { A := A * B ; B := B - 1 }
--   14..16 : move A to output R0; HALT

progFactM : List MInstr
progFactM =
  -- mul macro (0..6): r0 += r1 * r2 ; r1 := 0 ; r2 preserved ; returns to 11
  DECJZ R1 1 6 ∷
  DECJZ R2 2 4 ∷
  INC R0 3 ∷
  INC R3 1 ∷
  DECJZ R3 5 0 ∷
  INC R2 4 ∷
  DECJZ R3 11 11 ∷

  -- init (7): A := 1
  INC R1 8 ∷

  -- while test without consuming B (8..9); call mul (10)
  DECJZ R2 9 14 ∷
  INC R2 10 ∷
  DECJZ R3 0 0 ∷

  -- after mul: transfer R0 → R1 (11..12), then B-- and loop (13)
  DECJZ R0 12 13 ∷
  INC R1 11 ∷
  DECJZ R2 8 8 ∷

  -- done: move A → R0 (14..15), HALT (16)
  DECJZ R1 15 16 ∷
  INC R0 14 ∷
  HALT ∷
  []

compileMinsky : FactTask → MinskyCode
compileMinsky t = mkM 7 0 0 (n t) 0 progFactM

backendM : Backend FactTask MinskyCode
backendM = mkBackend compileMinsky UM

-- --------------------------------------------------------------------------
-- EVM compiler (stack + memory + jumps)
--
-- Memory convention:
--   mem[0] = A (accumulator)
--   mem[1] = B (counter)
--
-- The emitted code is a real loop using JUMPI/JUMP.

progFactE : ℕ → List EInstr
progFactE n₀ =
  -- init: mem[0] := 1; mem[1] := n₀
  PUSH 1 ∷ PUSH 0 ∷ MSTORE ∷
  PUSH n₀ ∷ PUSH 1 ∷ MSTORE ∷

  -- loopStart = 6
  PUSH 1 ∷ MLOAD ∷ PUSH 12 ∷ JUMPI ∷
  PUSH 27 ∷ JUMP ∷

  -- body (pc = 12)
  PUSH 1 ∷ MLOAD ∷ PUSH 0 ∷ MLOAD ∷ MUL ∷ PUSH 0 ∷ MSTORE ∷
  PUSH 1 ∷ MLOAD ∷ PUSH 1 ∷ SUB ∷ PUSH 1 ∷ MSTORE ∷
  PUSH 6 ∷ JUMP ∷

  -- end (pc = 27): push A; STOP
  PUSH 0 ∷ MLOAD ∷ STOP ∷
  []

compileEthereum : FactTask → EVMCode
compileEthereum t = mkE 0 [] mem0 (progFactE (n t))

backendE : Backend FactTask EVMCode
backendE = mkBackend compileEthereum UE
