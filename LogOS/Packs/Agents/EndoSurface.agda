{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.EndoSurface where

-- Shared “agent endomap” vocabulary:
-- both monitoring and learning are endomaps on boundary constraints.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Kernel.LogicKernel.Endo as LKEndo

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (S : AgentSocket Sig Q Task)
  where

  open AgentSocket S

  Policy : Set ℓ
  Policy = Con_bnd

  Endomap : Set (lsuc ℓ)
  Endomap = LKEndo.Endo LK

  apply : Endomap → Policy → Policy
  apply U = LKEndo.Endo.fn U

  ClosureStep : Set (lsuc ℓ)
  ClosureStep = LKEndo.ClosureStep LK

  applyStep : ClosureStep → Policy → Policy
  applyStep step = LKEndo.Endo.fn (LKEndo.ClosureStep.endo step)

