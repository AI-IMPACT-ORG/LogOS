{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Task where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

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

-- ============================================================================
-- A more general (still total) PA fragment: arithmetic expressions.
--
-- This is designed as a “task language” large enough to express non-trivial
-- arithmetic pipelines (polynomials, nested terms, etc.) while staying purely
-- structural/total (no unbounded loops).
-- ============================================================================

infixl 6 _+E_
infixl 7 _*E_

data PAExpr : Set where
  var : ℕ → PAExpr
  lit : ℕ → PAExpr
  _+E_ : PAExpr → PAExpr → PAExpr
  _*E_ : PAExpr → PAExpr → PAExpr

lookupDefaultℕ : ℕ → List ℕ → ℕ → ℕ
lookupDefaultℕ d []       _        = d
lookupDefaultℕ d (x ∷ _)  zero     = x
lookupDefaultℕ d (_ ∷ xs) (suc ix) = lookupDefaultℕ d xs ix

evalExpr : PAExpr → List ℕ → ℕ
evalExpr (var ix)  ρ = lookupDefaultℕ 0 ρ ix
evalExpr (lit n)   _ = n
evalExpr (e₁ +E e₂) ρ = evalExpr e₁ ρ + evalExpr e₂ ρ
evalExpr (e₁ *E e₂) ρ = evalExpr e₁ ρ * evalExpr e₂ ρ

record PAExprTask : Set lzero where
  constructor mkExprTask
  field
    expr : PAExpr
    env  : List ℕ

evalExprTask : PAExprTask → ℕ
evalExprTask t = evalExpr (PAExprTask.expr t) (PAExprTask.env t)
