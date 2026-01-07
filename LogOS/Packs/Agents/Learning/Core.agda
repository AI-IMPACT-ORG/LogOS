{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.Core where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.EndoSurface as EndoSurface

-- Learning is expressed in the same DSL as monitoring:
-- a policy is a boundary constraint, and a learning update is a monotone endomap.

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (S : AgentSocket Sig Q Task)
  where

  module E = EndoSurface.For S

  Policy : Set ℓ
  Policy = E.Policy

  Update : Set (lsuc ℓ)
  Update = E.Endomap

  apply : Update → Policy → Policy
  apply = E.apply

  -- A “learning step” is a closure step (id ≤ update ≤ Flow),
  -- so it can be composed and reasoned about via the endomap DSL.
  LearningStep : Set (lsuc ℓ)
  LearningStep = E.ClosureStep

  learnStep : LearningStep → Policy → Policy
  learnStep = E.applyStep
