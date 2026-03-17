{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.ContextApproximation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Context-indexed approximation contract (v1.1-native).
--
-- “Context” is intentionally general:
-- - scale is one context interpretation,
-- - time-slice is another,
-- - any directed budget/index discipline can be used.
--
-- This module is a refinement-first facade over the generic indexed
-- contractibility/boundary-gauge spine.

open import LogOS.Prelude
open import LogOS.LT.Theorems.BoundaryGauge using
    ( BoundaryGauge
    ; Contractive
    ; closeAt
    ; closeAt-weaken
    ; pathIndependenceAt
    ; noForkAt
    ; boundaryGaugeFiber
    )

import LogOS.LT.Theorems.Centering as Centering

record ContextApproximation
  {ℓC ℓB ℓ≤ ℓ≈ : Level}
  (Carrier : Set ℓC)
  (Context : Set ℓB)
  (_≤Ctx_ : Context → Context → Set ℓ≤)
  : Set (lsuc (ℓC ⊔ ℓB ⊔ ℓ≤ ⊔ ℓ≈)) where
  field
    gauge : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_
    contractive : Contractive gauge

  close : Context → Carrier → Set ℓ≈
  close = closeAt gauge

  close-weaken
    : ∀ {c c'} → _≤Ctx_ c c'
    → ∀ {x} → close c' x → close c x
  close-weaken = closeAt-weaken gauge

  -- Path-independence/no-fork (at each context index).
  pathIndependence
    : ∀ (c : Context) {x y : Carrier}
    → close c x
    → close c y
    → BoundaryGauge._≈At_ gauge c x y
  pathIndependence = pathIndependenceAt gauge

  noFork : ∀ (c : Context) {x y : Carrier} → BoundaryGauge._≈At_ gauge c x y
  noFork = noForkAt gauge contractive

  -- Re-expose as an indexed contractible fiber (for centering/acyclicity pattern).
  fiber
    : Centering.IndexedContractibleFiber Context Carrier (BoundaryGauge._≈At_ gauge)
  fiber = boundaryGaugeFiber gauge contractive

mkContextApproximation
  : ∀ {ℓC ℓB ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓB}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
  → (gauge : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → Contractive gauge
  → ContextApproximation Carrier Context _≤Ctx_
mkContextApproximation gauge contractive =
  record
    { gauge = gauge
    ; contractive = contractive
    }
