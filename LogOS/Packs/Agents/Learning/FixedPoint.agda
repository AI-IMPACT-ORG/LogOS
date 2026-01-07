{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.FixedPoint where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.LogicKernel using (LogicKernel)
import LogOS.Kernel.LogicKernel.Endo as LKEndo

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Learning.Core as LearningCore
open import LogOS.Theorems.Boundary.LogicKernel.Mu as LKMu

-- Learning fixed points via boundary Kleene mu.

module For
  {ℓ ℓTask : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (LogicKernel.BB (AgentSocket.LK Sock))))
  where

  open AgentSocket Sock
  open LearningCore.For Sock using (Policy; Update; apply; LearningStep)

  open LKEndo
  module Kμ = LKMu.Kleene Sig Q LK ωCPO
  open Kμ using (_⊑_; iter; μF; μF-unfold-left; μF-induction; ScottContinuous;
                 μF-unfold-right; iter-mono-chain-infl; μF-unfold-right-infl)

  iterPolicy : Update → ℕ → Policy
  iterPolicy U = iter (Endo.fn U)

  μPolicy : Update → Policy
  μPolicy U = μF (Endo.fn U)

  μPolicy-unfold-left
    : (U : Update)
    → _⊑_ (μPolicy U) (apply U (μPolicy U))
  μPolicy-unfold-left U = μF-unfold-left (Endo.fn U) (Endo.mono U)

  μPolicy-induction
    : (U : Update) (c : Policy)
    → _⊑_ (apply U c) c
    → _⊑_ (μPolicy U) c
  μPolicy-induction U c pre = μF-induction (Endo.fn U) (Endo.mono U) c pre

  iterPolicy-mono-chain
    : (U : Update)
    → (inflU : ∀ c → _⊑_ c (apply U c))
    → ∀ n → _⊑_ (iterPolicy U n) (iterPolicy U (suc n))
  iterPolicy-mono-chain U inflU = iter-mono-chain-infl (Endo.fn U) inflU

  μPolicy-unfold-right
    : (U : Update)
    → ScottContinuous (Endo.fn U)
    → (mono-chain : ∀ n → _⊑_ (iterPolicy U n) (iterPolicy U (suc n)))
    → _⊑_ (apply U (μPolicy U)) (μPolicy U)
  μPolicy-unfold-right U SC chain =
    μF-unfold-right (Endo.fn U) SC chain

  μPolicy-unfold-right-infl
    : (U : Update)
    → ScottContinuous (Endo.fn U)
    → (inflU : ∀ c → _⊑_ c (apply U c))
    → _⊑_ (apply U (μPolicy U)) (μPolicy U)
  μPolicy-unfold-right-infl U SC inflU =
    μF-unfold-right-infl (Endo.fn U) SC inflU

  stepUpdate : LearningStep → Update
  stepUpdate = ClosureStep.endo

  stepInfl : (s : LearningStep) → ∀ c → _⊑_ c (apply (stepUpdate s) c)
  stepInfl s c = ClosureStep.infl s c

  μPolicy-step : LearningStep → Policy
  μPolicy-step s = μPolicy (stepUpdate s)

  μPolicy-step-unfold-left
    : (s : LearningStep)
    → _⊑_ (μPolicy-step s) (apply (stepUpdate s) (μPolicy-step s))
  μPolicy-step-unfold-left s = μPolicy-unfold-left (stepUpdate s)

  μPolicy-step-unfold-right
    : (s : LearningStep)
    → ScottContinuous (Endo.fn (stepUpdate s))
    → _⊑_ (apply (stepUpdate s) (μPolicy-step s)) (μPolicy-step s)
  μPolicy-step-unfold-right s SC =
    μPolicy-unfold-right-infl (stepUpdate s) SC (stepInfl s)
