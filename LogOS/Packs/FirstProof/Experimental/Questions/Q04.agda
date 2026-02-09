{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.FirstProof.Experimental.Questions.Q04 where

-- Q04: Rooted polynomial convolution inequality.

open import LogOS.Prelude

import LogOS.Packs.FirstProof.Experimental.QuestionScaffold as QS

record Assumptions : Set1 where
  field
    PolynomialModel            : Set
    RealRootednessAxiom        : Set
    ConvolutionFormulaAxiom    : Set
    PotentialFunctionAxiom     : Set
    ExpectedAnswer             : Set

record Trace (A : Assumptions) : Set1 where
  open Assumptions A
  field
    encode-convolution         : ConvolutionFormulaAxiom
    control-roots              : RealRootednessAxiom
    compare-potential          : PotentialFunctionAxiom
    conclude-inequality        : ExpectedAnswer

Claim : Assumptions → Set
Claim A = Assumptions.ExpectedAnswer A

derive : (A : Assumptions) → Trace A → Claim A
derive A tr = Trace.conclude-inequality tr

question : QS.Question _ _ _
question = record
  { Assumptions = Assumptions
  ; Trace = Trace
  ; Claim = Claim
  ; derive = derive
  }

module Quartet = QS.Build question
open Quartet public using (Inputs; Pack; mkPack; assumptionsOf; claimOf)
