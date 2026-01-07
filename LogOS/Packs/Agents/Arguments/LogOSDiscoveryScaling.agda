{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Arguments.LogOSDiscoveryScaling where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Arguments.ScalingLaws as ScalingLaws

-- Discovery-driven scaling: "LogOS structure discovered during training"
-- is modeled as a downward-closed, RG-stable predicate on policies.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RG = RGFlow.For K ωCPO
  module SL = ScalingLaws.For K ωCPO

  open RG using (Policy; RGStep; RGStable; ScalingDimension; rg-μ; rg-least-stable)
  open RG.μ using (_⊑_)
  open QAdapter Q using (_≤s_)
  open GradedKernel K using (Code; decode; reify; reify-decode)

  record DiscoveryAssumptions {g : QAdapter.Scale Q} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      Discover : Policy → Set ℓ
      -- Downward closed: if a stronger policy is discovered, so is any refinement.
      down : ∀ {c d} → _⊑_ c d → Discover d → Discover c
      -- Discovery implies RG-stability.
      stable : ∀ {c} → Discover c → RGStable s c
      -- Order parameter / scaling dimension for the RG step.
      dim : ScalingDimension s

  open DiscoveryAssumptions public

  DiscoverCode : ∀ {g} {s : RGStep g} → DiscoveryAssumptions s → Code → Set ℓ
  DiscoverCode A γ = Discover A (decode γ)

  discover-reify
    : ∀ {g} {s : RGStep g} (A : DiscoveryAssumptions s) γ
    → DiscoverCode A (reify γ) ↔ DiscoverCode A γ
  discover-reify A γ =
    let eq = reify-decode γ in
    record
      { to   = λ d → subst (Discover A) eq d
      ; from = λ d → subst (Discover A) (sym eq) d
      }

  -- Root-cause lemma: any discovered RG-stable policy forces discovery at rg-μ.
  discovery-root
    : ∀ {g} {s : RGStep g} (A : DiscoveryAssumptions s)
    → ∀ {c} → Discover A c → Discover A (rg-μ s)
  discovery-root {s = s} A d =
    let st = stable A d
        le = rg-least-stable s st
    in down A le d

  -- Phase-transition witness: discovery becomes true at the least RG-stable policy.
  record PhaseTransition {g} {s : RGStep g} (A : DiscoveryAssumptions s) : Set (lsuc ℓ) where
    field
      witness : Σ Policy (Discover A)

  transition-root
    : ∀ {g} {s : RGStep g} {A : DiscoveryAssumptions s}
    → PhaseTransition A
    → Discover A (rg-μ s)
  transition-root {s = s} {A = A} pt =
    discovery-root {s = s} A (proj₂ (PhaseTransition.witness pt))

  -- Scaling law consequence for discovered codes.
  discovery-scalingBound
    : ∀ {g} {s : RGStep g} (A : DiscoveryAssumptions s) {γ}
    → DiscoverCode A γ
    → SL.ScalingBound s (dim A) γ
  discovery-scalingBound {s = s} A d =
    SL.scalingBound-from-stable s (dim A) (stable A d)
