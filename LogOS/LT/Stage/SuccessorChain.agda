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

-- Canonical finite-successor stage carrier for LT ω-style constructions.
--
-- This is intentionally *not* exposed as host nat. LT-core uses an explicit
-- stage datatype so sigma/omega completeness and iteration stay independent of
-- the host numeric surface.

data Stageω : Set where
  zero : Stageω
  suc  : Stageω -> Stageω

iterω : ∀ {ℓ} {A : Set ℓ} -> (A -> A) -> Stageω -> A -> A
iterω f zero    x = x
iterω f (suc n) x = iterω f n (f x)

infix 4 _≤ω_

data _≤ω_ : Stageω -> Stageω -> Set where
  z≤ω : ∀ {n} -> zero ≤ω n
  s≤ω : ∀ {m n} -> m ≤ω n -> suc m ≤ω suc n

≤ω-refl : ∀ {n} -> n ≤ω n
≤ω-refl {zero}  = z≤ω
≤ω-refl {suc n} = s≤ω ≤ω-refl

maxω : Stageω -> Stageω -> Stageω
maxω zero    n       = n
maxω (suc m) zero    = suc m
maxω (suc m) (suc n) = suc (maxω m n)

≤ω-maxL : ∀ m n -> m ≤ω maxω m n
≤ω-maxL zero    _       = z≤ω
≤ω-maxL (suc m) zero    = ≤ω-refl
≤ω-maxL (suc m) (suc n) = s≤ω (≤ω-maxL m n)

≤ω-maxR : ∀ m n -> n ≤ω maxω m n
≤ω-maxR zero    n       = ≤ω-refl
≤ω-maxR (suc m) zero    = z≤ω
≤ω-maxR (suc m) (suc n) = s≤ω (≤ω-maxR m n)
