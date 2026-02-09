{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.FirstProof.Experimental.Questions.Q02 where

-- Q02: Local Rankin-Selberg nonvanishing with Whittaker test vectors.

open import LogOS.Prelude

import LogOS.Packs.FirstProof.Experimental.QuestionScaffold as QS

record Assumptions : Set1 where
  field
    LocalFieldModel            : Set
    RepresentationGLnPlus1     : Set
    RepresentationGLn          : Set
    WhittakerCompatibility     : Set
    IntegralConvergenceAxiom   : Set
    ExpectedAnswer             : Set

record Trace (A : Assumptions) : Set1 where
  open Assumptions A
  field
    choose-test-vector         : WhittakerCompatibility
    establish-convergence      : IntegralConvergenceAxiom
    prove-nonvanishing         : ExpectedAnswer

Claim : Assumptions → Set
Claim A = Assumptions.ExpectedAnswer A

derive : (A : Assumptions) → Trace A → Claim A
derive A tr = Trace.prove-nonvanishing tr

question : QS.Question _ _ _
question = record
  { Assumptions = Assumptions
  ; Trace = Trace
  ; Claim = Claim
  ; derive = derive
  }

module Quartet = QS.Build question
open Quartet public using (Inputs; Pack; mkPack; assumptionsOf; claimOf)
