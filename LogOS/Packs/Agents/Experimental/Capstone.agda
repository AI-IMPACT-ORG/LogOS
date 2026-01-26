{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Capstone where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Closure using (ClosureOp)
open import LogOS.Boundary.Telemetry using (TelemetryTrace)
open import LogOS.Prelude.NatOrder using (_≤ℕ_)
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded.Endo as GEndo
import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFrom
import LogOS.Kernel.LogicKernel.EndoRelative as EndoRel

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Physics.LearningCost as LearningCost
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

import LogOS.Domain.Complexity.MeasurementCapacity as MC
import LogOS.Domain.Complexity.DataProcessingInequality as DPI
import LogOS.Theorems.Meta.SpectralSeparationOutput as SSO
open import LogOS.Theorems.Meta.Assumptions.Diagonal using (TruthDiagonal)
import LogOS.Theorems.Meta.LandauerIO as LIO

-- Experimental capstones: RG flow stability + forcing + budgets + physics.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  open GradedKernel K using (BB)
  open BulkBoundary BB using (Con_bnd)

  module RG = RGFlow.For K ωCPO
  open RG using (Policy; RGStep; applyRG; rg-μ; rg-induction)
  open GEndo using (Endo; _≤₂_; Flow-EndoAt; mkClosureStepAt)

  private
    CP = BulkBoundary.bnd BB
    _⊑_ = ConPreorder._⊑_ CP

  module Forcing
    (C : ClosureOp (BulkBoundary.bnd BB))
    (g : QAdapter.Scale Q)
    where

    private
      LK = LKFrom.asLogicKernel K

    module JRel = EndoRel.FromClosureOp LK C

    J : Endo K
    J = GEndo.fromLKEndo JRel.J

    JClosureStep : Set (lsuc ℓ)
    JClosureStep = JRel.ClosureStep

    JClosed : Policy → Set ℓ
    JClosed c = _⊑_ (Endo.fn J c) c

    toRGStep
      : (J≤FlowAt : _≤₂_ K J (Flow-EndoAt K g))
      → JClosureStep → RGStep g
    toRGStep J≤FlowAt s =
      mkClosureStepAt
        (GEndo.fromLKEndo (JRel.endo s))
        (JRel.infl s)
        (λ c → ConPreorder.trans CP (JRel.leJ s c) (J≤FlowAt c))

    goal-preserved
      : (J≤FlowAt : _≤₂_ K J (Flow-EndoAt K g))
      → (s : JClosureStep) (goal : Policy)
      → JClosed goal
      → _⊑_ (applyRG (toRGStep J≤FlowAt s) goal) goal
    goal-preserved _ s goal closed =
      ConPreorder.trans CP (JRel.leJ s goal) closed

    rg-least-stable
      : (J≤FlowAt : _≤₂_ K J (Flow-EndoAt K g))
      → (s : JClosureStep) (c : Policy)
      → _⊑_ (applyRG (toRGStep J≤FlowAt s) c) c
      → _⊑_ (rg-μ (toRGStep J≤FlowAt s)) c
    rg-least-stable J≤FlowAt s c pre =
      rg-induction (toRGStep J≤FlowAt s) c pre

    rg-goal-fixed
      : (J≤FlowAt : _≤₂_ K J (Flow-EndoAt K g))
      → (s : JClosureStep) (goal : Policy)
      → JClosed goal
      → _⊑_ (rg-μ (toRGStep J≤FlowAt s)) goal
    rg-goal-fixed J≤FlowAt s goal closed =
      rg-induction (toRGStep J≤FlowAt s) goal (goal-preserved J≤FlowAt s goal closed)

  module Physics
    {ℓTask : Level}
    {Task : Set ℓTask}
    (Sock : AgentSocket Sig Q Task)
    where

    open LogOSSignature Sig using (Cosp)

    module LC = LearningCost.For Sock
    module G = LC.Graded K

    record RGPhysicsAssumptions {ℓT : Level} (T : TelemetryTrace ℓT)
      : Set (lsuc (lsuc (ℓ ⊔ ℓT))) where
      field
        landauer : G.SoftLearningAssumptions
        condensation : G.SoftLearningCondensationAssumptions T

    rg-physics-summary
      : ∀ {ℓT} {T : TelemetryTrace ℓT}
      → (A : RGPhysicsAssumptions T)
      → ∀ {g} (C : DPI.Channel Cosp) (s : RGStep g)
      → QAdapter._≤s_ Q
          (LIO.LandauerIOAssumptions.L (G.SoftLearningAssumptions.landauer (RGPhysicsAssumptions.landauer A)))
          (LIO.LandauerIOAssumptions.cost (G.SoftLearningAssumptions.landauer (RGPhysicsAssumptions.landauer A))
            (G.SoftLearningAssumptions.stepProgram (RGPhysicsAssumptions.landauer A) s))
        ×
        MC.MeasurementCapacity.info
          (LC.CondensationAssumptions.capacity
            (G.soft-condensation
              (RGPhysicsAssumptions.condensation A)))
          (DPI.Channel.run C (G.SoftLearningCondensationAssumptions.stepProgram
            (RGPhysicsAssumptions.condensation A) s))
          ≤ℕ
        MC.mul
          (MC.MeasurementCapacity.κ
            (LC.CondensationAssumptions.capacity
              (G.soft-condensation
                (RGPhysicsAssumptions.condensation A))))
          (MC.MeasurementCapacity.meas
            (LC.CondensationAssumptions.capacity
              (G.soft-condensation
                (RGPhysicsAssumptions.condensation A)))
            (G.SoftLearningCondensationAssumptions.stepProgram
              (RGPhysicsAssumptions.condensation A) s))
    rg-physics-summary A C s =
      G.soft-learning-cost (RGPhysicsAssumptions.landauer A) s ,
      G.soft-learning-condensation (RGPhysicsAssumptions.condensation A) C s

module BudgetedOpacity
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {K   : Kernel Sig Q}
  (O   : SSO.SpectralSeparationOutput K)
  where

  open Kernel K
  module GB = SSO.GeneralB O

  module WithBudget
    (CB : GB.WitnessCostB (QAdapter.Scale Q))
    where

    module G  = GB.General (QAdapter.Scale Q) (QAdapter._≤s_ Q) CB
    open G using (WithinBudget)

    no-total-budgeted-eval
      : ∀ (Bnd : Code → QAdapter.Scale Q)
      → TruthDiagonal K (WithinBudget Bnd)
      → ¬ (∀ γ → WithinBudget Bnd γ)
    no-total-budgeted-eval = G.no-total-within-budgetK

    diagonal-witness-budgeted
      : ∀ (Bnd : Code → QAdapter.Scale Q)
      → TruthDiagonal K (WithinBudget Bnd)
      → Σ Code (λ γ → ¬ WithinBudget Bnd γ)
    diagonal-witness-budgeted = G.diagonal-witness-within-budgetK
