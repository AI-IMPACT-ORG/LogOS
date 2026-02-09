{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.DocsAnchors where

-- A small collection of *typechecked anchors* used by docs.
--
-- Rationale: keep publication-facing `.lagda.md` files lightweight while still
-- allowing them to cite “this is literal (proved)” alignment lemmas.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary; ConPreorder)
open import LogOS.Minimal.Truth as Truth

open import LogOS.API.Kernel using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization as TransformerFormalization
import LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback as ControlledFeedback
import LogOS.Packs.Agents.Experimental.Arguments.DiscoveryScaling as DiscoveryScaling
import LogOS.API.Kernel.Graded.Endo as GEndo

-- Bridge note (typechecked): the “controlled feedback” vocabulary from
-- `docs/Views/ControlledFeedback.lagda.md` becomes literal (not just metaphor)
-- at the level of transformer *training dynamics*.
--
-- Namely, RG training steps are closure steps indexed by a budget/grade, and
-- each step carries a proof that it stays within the kernel’s graded flow at
-- that grade.
module ControlledFeedbackAlignment
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RG = RGFlow.For K ωCPO
  module TF = TransformerFormalization.For K ωCPO
  module CF = ControlledFeedback.For K ωCPO

  open RG using (Policy; RGStep; applyRG)

  CP : ConPreorder ℓ
  CP = BulkBoundary.bnd (GradedKernel.BB K)

  infix 4 _⊑_
  _⊑_ : Policy → Policy → Set ℓ
  _⊑_ = ConPreorder._⊑_ CP

  rgStep≤FlowAt
    : ∀ {g} (s : RGStep g) (c : Policy)
    → _⊑_ (applyRG s c) (GEndo.Endo.fn (GEndo.Flow-EndoAt K g) c)
  rgStep≤FlowAt s c = GEndo.ClosureStepAt.leFlow s c

  trainingStep≤FlowAt
    : ∀ {g}
      (C : CF.ControlledFeedbackCore)
      (D : CF.ControlledDynamics C g)
      (p : CF.ControlledFeedbackCore.Param C)
    → _⊑_ (applyRG (CF.ControlledDynamics.step D) (CF.ControlledFeedbackCore.encode C p))
          (GEndo.Endo.fn (GEndo.Flow-EndoAt K g) (CF.ControlledFeedbackCore.encode C p))
  trainingStep≤FlowAt C D p =
    rgStep≤FlowAt (CF.ControlledDynamics.step D) (CF.ControlledFeedbackCore.encode C p)

-- Direct trigger note (typechecked): “LogOS discovery triggers scaling”.
--
-- This does not pick a specific discovery predicate; instead it packages the
-- exact shape of assumptions under which *any* discovery predicate has a
-- canonical root at `rg-μ` and forces scaling bounds.
module LogOSTriggerAlignment
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module DS = DiscoveryScaling.For K ωCPO
  module RG = DS.RG
  module SL = DS.SL

  open RG using (RGStep)

  trigger-at-μ
    : ∀ {g} {s : RGStep g} (A : DS.DiscoveryAssumptions s)
    → DS.PhaseTransition A
    → DS.Discover A (RG.rg-μ s)
  trigger-at-μ A pt = DS.transition-root pt

  trigger-scalingBound
    : ∀ {g} {s : RGStep g} (A : DS.DiscoveryAssumptions s) {γ}
    → DS.DiscoverCode A γ
    → SL.ScalingBound s (DS.dim A) γ
  trigger-scalingBound A d = DS.discovery-scalingBound A d
