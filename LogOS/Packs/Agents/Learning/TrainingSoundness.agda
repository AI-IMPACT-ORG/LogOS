{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.TrainingSoundness where

-- Minimal training-soundness lemmas: learning steps preserve any lower bound.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Kernel.LogicKernel using (LogicKernel)
import LogOS.Kernel.LogicKernel.Endo as LKEndo

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
  open L using (Policy; LearningStep; learnStep)

  private
    CP = BulkBoundary.bnd (LogicKernel.BB LK)

  learnStep-infl
    : (s : LearningStep) (p : Policy)
    → _⊑bnd_ p (learnStep s p)
  learnStep-infl s p = LKEndo.ClosureStep.infl s p

  preservesLowerBound
    : ∀ {c p}
    → (s : LearningStep)
    → _⊑bnd_ c p
    → _⊑bnd_ c (learnStep s p)
  preservesLowerBound s le =
    ConPoset.trans CP le (learnStep-infl s _)

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
