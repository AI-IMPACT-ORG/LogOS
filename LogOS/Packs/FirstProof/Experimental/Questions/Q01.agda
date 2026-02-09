{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.FirstProof.Experimental.Questions.Q01 where

-- Q01: Phi^4_3 shift quasi-invariance.

open import LogOS.Prelude

import LogOS.Packs.FirstProof.Experimental.QuestionScaffold as QS

record Assumptions : Set1 where
  field
    PhaseSpace                 : Set
    ShiftAction                : Set
    QuasiInvarianceHypothesis  : Set
    RenormalisationHypothesis  : Set
    ExpectedAnswer             : Set

record Trace (A : Assumptions) : Set1 where
  open Assumptions A
  field
    setup-step    : QuasiInvarianceHypothesis
    renorm-step   : RenormalisationHypothesis
    answer-step   : ExpectedAnswer

Claim : Assumptions → Set
Claim A = Assumptions.ExpectedAnswer A

derive : (A : Assumptions) → Trace A → Claim A
derive A tr = Trace.answer-step tr

question : QS.Question _ _ _
question = record
  { Assumptions = Assumptions
  ; Trace = Trace
  ; Claim = Claim
  ; derive = derive
  }

module Quartet = QS.Build question
open Quartet public using (Inputs; Pack; mkPack; assumptionsOf; claimOf)
