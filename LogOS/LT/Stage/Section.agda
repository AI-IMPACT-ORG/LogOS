{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stage.Section where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- A coherent family indexed by a successor chain.
--
-- The section itself carries no extra laws beyond totality over the chosen
-- stage carrier. Coherence is expressed by packaging one `at` map instead of
-- passing unrelated stage-local records around.

open import LogOS.Prelude
open import LogOS.LT.Stage.SuccessorChain using (SuccessorChain; StageOf)

record Section
  {ℓ : Level}
  {Stage : Set ℓ}
  (C : SuccessorChain Stage)
  {ℓFiber : Stage -> Level}
  (Fiber : (i : Stage) -> Set (ℓFiber i))
  : Setω where
  field
    at : (i : StageOf C) -> Fiber i

open Section public
