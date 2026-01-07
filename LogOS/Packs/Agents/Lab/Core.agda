{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Lab.Core where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.MultiIO using (MultiBoundaryIO)
open import LogOS.Kernel.LogicKernel using (LogicKernel)
import LogOS.Kernel.Graded as GK

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Learning.Core as LearningCore
import LogOS.Packs.Agents.Learning.FixedPoint as LearningMu
import LogOS.Packs.Agents.Learning.SoftPolicy as Soft
import LogOS.Packs.Agents.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Physics.MaxwellAgent as MaxwellAgent
import LogOS.Packs.Agents.Physics.LearningCost as LearningCost
import LogOS.Packs.Agents.Networks.Roles as Roles

-- A lab surface: socket + learning + physics + network observability.

module For
  {ℓ ℓTask : Level}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {Task : Set ℓTask}
  (Sock : AgentSocket Sig Q Task)
  where

  open AgentSocket Sock public

  module Learning = LearningCore.For Sock
  module Physics  = LearningCost.For Sock
  module Maxwell  = MaxwellAgent.For Sock

  module WithMu
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
              (BulkBoundary.bnd (LogicKernel.BB LK)))
    where
    module Mu = LearningMu.For Sock ωCPO

  module Network (Role : Set ℓ) where
    M : MultiBoundaryIO Role Sig Q (LogicKernel.HWorld LK) (LogicKernel.BB LK) (LogicKernel.HTruth LK)
    M = multiBoundaryIO Role

    module Obs = Roles.For M
    open Obs public

  module Graded (K : GK.GradedKernel Sig Q) where
    module SoftPolicy = Soft.For K
    module LC = LearningCost.For Sock
    module SoftPhysics = LC.Graded K
    module RG (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
                      (BulkBoundary.bnd (GK.GradedKernel.BB K))) where
      module Flow = RGFlow.For K ωCPO
