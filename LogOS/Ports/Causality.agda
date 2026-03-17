{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Causality where

-- Causality vocabulary (v1.1-native).
--
-- In the LogOS 1.1 core, the *concrete* causal ingredient is the Flow/closure
-- doctrine on boundary constraints:
--
-- - a causal boundary has a guarded closure `Flow` (monotone, inflationary,
--   lax-idempotent),
-- - a causal translation preserves it via the single lax inequality
--     map∂ (Flow c) ⊑ Flow (map∂ c).
--
-- This module provides "causal" aliases for the existing Flow-layer names,
-- so downstream code can adopt locality/causality language without renaming the
-- kernel core.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Flow using (GuardedClosure; Stable) renaming (Flow to Cause)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.LT.Kernel using (Kernel; bnd)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

import LogOS.LT.Ports.PortStack.Raw as PortStack
import LogOS.LT.LOG.Flow2Cat as Flow2Cat

-- Aliases (no new primitives).

CausalClosure : ∀ {ℓCon ℓRel} → ConPreorder ℓCon ℓRel → Set (lsuc (ℓCon ⊔ ℓRel))
CausalClosure = GuardedClosure

CausalStable = Stable

CausalHom = KernelHomFlow

CausalKernel : ∀ {ℓ ℓRel ℓCode : Level} → Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
CausalKernel {ℓ} {ℓRel} {ℓCode} =
  Thin2Cat.Obj (Flow2Cat.WithPort {ℓ} {ℓRel} {ℓCode})

CausalKernelHom
  : ∀ {ℓ ℓRel ℓCode : Level}
  → CausalKernel {ℓ} {ℓRel} {ℓCode}
  → CausalKernel {ℓ} {ℓRel} {ℓCode}
  → Set _
CausalKernelHom {ℓ} {ℓRel} {ℓCode} X Y =
  Con (Thin2Cat.Hom (Flow2Cat.WithPort {ℓ} {ℓRel} {ℓCode}) X Y)

LOGᶜ = Flow2Cat.WithPort

forgetCausal = Flow2Cat.forget

causalKernel
  : ∀ {ℓ ℓRel ℓCode : Level}
  → CausalKernel {ℓ} {ℓRel} {ℓCode}
  → Kernel ℓ ℓRel ℓCode
causalKernel {ℓ} {ℓRel} {ℓCode} =
  PortStack.baseObj {S = Flow2Cat.stack {ℓ} {ℓRel} {ℓCode}}

causalClosure
  : ∀ {ℓ ℓRel ℓCode : Level}
  → (X : CausalKernel {ℓ} {ℓRel} {ℓCode})
  → GuardedClosure (bnd (causalKernel X))
causalClosure {ℓ} {ℓRel} {ℓCode} X =
  PortStack.getObj (Flow2Cat.port {ℓ} {ℓRel} {ℓCode}) X
