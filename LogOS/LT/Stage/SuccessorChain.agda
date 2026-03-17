{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stage.SuccessorChain where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Minimal successor-chain indexing for staged constructions.
--
-- This is intentionally small: it provides only a carrier of stages and one
-- successor step. The point is to package coherent stage-indexed sections, not
-- to assert any generic transfinite/fixed-point theorem.

open import LogOS.Prelude

record SuccessorChain {ℓ : Level} (Carrier : Set ℓ) : Set ℓ where
  field
    next : Carrier -> Carrier

open SuccessorChain public

StageOf : ∀ {ℓ : Level} {Carrier : Set ℓ} -> SuccessorChain Carrier -> Set ℓ
StageOf {Carrier = Carrier} _ = Carrier

levelChain : SuccessorChain Level
levelChain = record { next = lsuc }
