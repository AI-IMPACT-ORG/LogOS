{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Telemetry where

-- Telemetry contracts for agent sockets: observation-only ports on policies.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Boundary.Telemetry
open import LogOS.Kernel.LogicKernel using (LogicKernel)
import LogOS.Kernel.LogicKernel.Endo as LKEndo

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Learning.Core as LearningCore

module For
  {ℓ ℓTask ℓT : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  (T : TelemetryTrace ℓT)
  where

  open AgentSocket Sock
  module L = LearningCore.For Sock
  open L using (LearningStep; learnStep)
  open TelemetryTrace T using (Trace; _⊑T_)

  record TelemetryContract : Set (lsuc (ℓ ⊔ ℓT)) where
    field
      port
        : BoundaryTelemetryPort
            Sig Q (LogicKernel.HWorld LK) (LogicKernel.BB LK) (LogicKernel.HTruth LK)
            boundaryIO T

    open BoundaryTelemetryPort port public
      using (observe-bnd; observe-bnd-mono; observe-bnd-respects)

    telemetry-step
      : ∀ (s : LearningStep) (p : Con_bnd)
      → _⊑T_ (observe-bnd p) (observe-bnd (learnStep s p))
    telemetry-step s p = observe-bnd-mono (LKEndo.ClosureStep.infl s p)
