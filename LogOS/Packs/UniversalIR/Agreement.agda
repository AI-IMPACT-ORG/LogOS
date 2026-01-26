{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Agreement where

-- Curated, paper-facing surface for the “one algorithm, many paradigms, same
-- run” agreement theorem.

open import LogOS.Domain.UniversalIR.Theorems public
  using (ParadigmsCorrect; ParadigmsRunEq; patask-paradigms-correct; patask-paradigms-runEq)

five-paradigm-correct = patask-paradigms-correct

five-paradigm-agreement : ParadigmsRunEq
five-paradigm-agreement = patask-paradigms-runEq

-- A strictly more expressive (but still total) task language: arithmetic expressions.
--
-- This is “more general tasks” in the sense of a larger input language.
-- The compilers in `TheoremsExpr` are extensional (compile-by-observation).

open import LogOS.Domain.UniversalIR.TheoremsExpr public
  using
    ( ExprParadigmsCorrect
    ; ExprParadigmsRunEq
    ; paexprtask-paradigms-correct
    ; paexprtask-paradigms-runEq
    )

five-paradigm-expr-correct = paexprtask-paradigms-correct

five-paradigm-expr-agreement : ExprParadigmsRunEq
five-paradigm-expr-agreement = paexprtask-paradigms-runEq
