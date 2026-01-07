{-
LogOS: an Agda research library for foundational logic system architecture.
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
