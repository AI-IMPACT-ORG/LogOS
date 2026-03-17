{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CrossStageReificationPort where

-- Cross-stage predicate reification:
-- reify predicates on a source set context as sets in a larger target context.
--
-- This is the honest interface for cumulative-hierarchy steps:
-- same-stage unrestricted comprehension is avoided, but a successor stage may
-- represent source predicates as target-stage sets.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.Syntax.Prop using (_↔_)

import LogOS.Ports.Reification.CrossStage as Core

open import LogOS.Apps.ZFC.Stack.Boundary using (PredicateBoundary)
open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)

record CrossStagePredicateReification
  {ℓ₀ ℓ₁ : Level}
  (C₀ : SetContext {ℓ₀})
  (C₁ : SetContext {ℓ₁})
  : Set (lsuc (lsuc (ℓ₀ ⊔ ℓ₁))) where

  private
    module Src = SetContext C₀
    module Tgt = SetContext C₁

  PredBnd₀ = PredicateBoundary Src.SetU
  Predicate₀ = Con PredBnd₀

  field
    embed : Src.SetU → Tgt.SetU

    Reifiable : Predicate₀ → Set (lsuc (ℓ₀ ⊔ ℓ₁))

    reify : (P : Predicate₀) → Reifiable P → Tgt.SetU

    mem-reify↔
      : ∀ (P : Predicate₀) (rP : Reifiable P) z
      → (embed z Tgt.∈ reify P rP) ↔ P z

  core
    : Core.CrossStageReification
        Src.SetU
        Tgt.SetU
        (λ z y → embed z Tgt.∈ y)
  core =
    record
      { Reifiable = Reifiable
      ; reify = reify
      ; probe-reify↔ = mem-reify↔
      }

open CrossStagePredicateReification public
