{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Language where

open import LogOS.Prelude

-- A tiny While language over two variables.
--
-- This is intentionally small but already supports unbounded looping via `whileNZ`
-- and a non-trivial arithmetic primitive (`mulAB`), enough to express factorial.

data Var : Set where
  A B : Var

infixr 5 _>>_

data Stmt : Set where
  skip    : Stmt
  inc     : Var → Stmt
  dec     : Var → Stmt
  mulAB   : Stmt                 -- A := A * B  (B is preserved)
  _>>_    : Stmt → Stmt → Stmt
  whileNZ : Var → Stmt → Stmt    -- while v ≠ 0: body

-- Small derived combinators used in examples.

clear : Var → Stmt
clear v = whileNZ v (dec v)

set1 : Var → Stmt
set1 v = clear v >> inc v

-- Factorial program (expects input in B, returns output in A).
--
--   A := 1
--   while B ≠ 0:
--     A := A * B
--     B := B - 1

factorial : Stmt
factorial = set1 A >> whileNZ B (mulAB >> dec B)
