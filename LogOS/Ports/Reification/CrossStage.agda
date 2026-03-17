{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Reification.CrossStage where

-- Cross-stage reification (pure bridge; no `Flow`).
--
-- This is the honest interface for successor-stage comprehension:
-- a target stage may represent predicates on a source stage, while avoiding
-- same-stage unrestricted comprehension.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

record CrossStageReification
  {ℓI ℓX ℓProbe ℓPred ℓR : Level}
  (I : Set ℓI)
  (X : Set ℓX)
  (probe : I → X → Set ℓProbe)
  : Set (lsuc (ℓI ⊔ ℓX ⊔ ℓProbe ⊔ ℓPred ⊔ ℓR)) where

  field
    -- Admissibility ledger over predicate families on `I`.
    Reifiable : (I → Set ℓPred) → Set ℓR

    -- Reify an admissible predicate family as a point in `X`.
    reify : (P : I → Set ℓPred) → Reifiable P → X

    -- Correctness: probing the reified point matches the predicate family.
    probe-reify↔ : ∀ P r i → probe i (reify P r) ↔ P i

open CrossStageReification public

