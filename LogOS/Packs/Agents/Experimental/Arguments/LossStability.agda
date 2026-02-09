{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.LossStability where

-- Small generic bridge:
-- if a numeric/graded observable decreases and its order reflects the policy
-- order, then the policy is RG-stable.
--
-- This is used by the transformer scaling pipeline, but is intentionally not
-- transformer-specific.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.API.Kernel using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.Context as Ctx

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RG = RGFlow.For K ωCPO

  open RG using (Policy; RGStep; RGStable; applyRG)
  open RG.μ using (_⊑_)
  open QAdapter Q using (Scale; _≤s_)

  -- Order-reflection: the observable order implies the underlying policy order.
  record LossOrderReflecting (obs : Policy → Scale) : Set (lsuc (lsuc ℓ)) where
    field
      reflect : ∀ {c d} → _≤s_ (obs c) (obs d) → _⊑_ c d

  -- If `obs` decreases along the step, order-reflection yields RG stability.
  lossDecrease-stable
    : ∀ {g} {s : RGStep g} (obs : Policy → Scale)
    → LossOrderReflecting obs
    → (∀ c → _≤s_ (obs (applyRG s c)) (obs c))
    → ∀ c → RGStable s c
  lossDecrease-stable obs O dec c =
    record { closed = LossOrderReflecting.reflect O (dec c) }

-- Context-bundled entrypoint (convenience).
module ForCtx
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (C : Ctx.Context Sig Q)
  where
  open For (Ctx.Context.K C) (Ctx.Context.ωCPO C) public
