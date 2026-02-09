{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.TrainingSoundness where

-- Minimal training-soundness lemmas: learning steps preserve any lower bound.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Kernel using (Kernel)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Learning.Core as LearningCore

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  where

  open AgentSocket Sock
  module L = LearningCore.For Sock
  open L using (Policy; LearningStep; learnStep; learnStep-infl)

  private
    CP = BulkBoundary.bnd (Kernel.BB LK)

  preservesLowerBound
    : ∀ {c p}
    → (s : LearningStep)
    → _⊑bnd_ c p
    → _⊑bnd_ c (learnStep s p)
  preservesLowerBound s le =
    ConPreorder.trans CP le (learnStep-infl s _)

  preservesSafety
    : ∀ {p}
    → (s : LearningStep)
    → _⊑bnd_ SafetySem p
    → _⊑bnd_ SafetySem (learnStep s p)
  preservesSafety s = preservesLowerBound s

  preservesObjective
    : ∀ {p}
    → (s : LearningStep)
    → _⊑bnd_ ObjectiveSem p
    → _⊑bnd_ ObjectiveSem (learnStep s p)
  preservesObjective s = preservesLowerBound s

  preservesAssumes
    : ∀ {p}
    → (s : LearningStep)
    → _⊑bnd_ AssumesSem p
    → _⊑bnd_ AssumesSem (learnStep s p)
  preservesAssumes s = preservesLowerBound s
