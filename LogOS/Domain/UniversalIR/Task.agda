{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Task where

open import LogOS.Prelude

-- A tiny fragment of PA tasks: binary arithmetic on two naturals.

data PAOp : Set where
  Add Mul : PAOp

record PATask : Set lzero where
  constructor mkTask
  field
    op  : PAOp
    a b : ℕ

eval : PATask → ℕ
eval t with PATask.op t
... | Add = (PATask.a t) + (PATask.b t)
... | Mul = (PATask.a t) * (PATask.b t)
