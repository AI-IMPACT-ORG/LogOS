{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.BoundaryGauge where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Context-indexed boundary gauge (refinement-first).
--
-- Reading:
-- - `BoundaryGauge` is a context-indexed relation with one distinguished center.
-- - `closeAt c x` means "x is c-close to the center".
-- - `Contractive` adds the canonical theorem shape: every point contracts to
--   the same center at every context.
--
-- This is the quantitative/lax counterpart of the cone/contractibility story:
-- closeness is indexed by contexts, and path-independence follows from
-- symmetry+transitivity at each index.

open import LogOS.Prelude
import LogOS.LT.Theorems.Centering as Centering

record BoundaryGauge
  {ℓC ℓB ℓ≤ ℓ≈ : Level}
  (Carrier : Set ℓC)
  (Context : Set ℓB)
  (_≤Ctx_ : Context → Context → Set ℓ≤)
  : Set (lsuc (ℓC ⊔ ℓB ⊔ ℓ≤ ⊔ ℓ≈)) where
  infix 4 _≈At_

  field
    center : Carrier
    _≈At_ : Context → Carrier → Carrier → Set ℓ≈

    symAt : ∀ {c x y} → _≈At_ c x y → _≈At_ c y x

    transAt : ∀ {c x y z} → _≈At_ c x y → _≈At_ c y z → _≈At_ c x z

    weakenAt
      : ∀ {c c'}
      → _≤Ctx_ c c'
      → ∀ {x y}
      → _≈At_ c' x y
      → _≈At_ c x y

  closeAt : Context → Carrier → Set ℓ≈
  closeAt c x = _≈At_ c x center

  closeAt-weaken
    : ∀ {c c'}
    → _≤Ctx_ c c'
    → ∀ {x}
    → closeAt c' x
    → closeAt c x
  closeAt-weaken cc' = weakenAt cc'

open BoundaryGauge public
record Contractive
  {ℓC ℓB ℓ≤ ℓ≈ : Level}
  {Carrier : Set ℓC}
  {Context : Set ℓB}
  {_≤Ctx_ : Context → Context → Set ℓ≤}
  (G : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  : Set (lsuc (ℓC ⊔ ℓB ⊔ ℓ≤ ⊔ ℓ≈)) where
  field
    contractAt
      : ∀ (c : Context)
      → (x : Carrier)
      → BoundaryGauge.closeAt G c x

open Contractive public
centerClosed
  : ∀ {ℓC ℓB ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓB}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → Contractive G
  → ∀ (c : Context)
  → BoundaryGauge.closeAt G c (BoundaryGauge.center G)
centerClosed G C c = Contractive.contractAt C c (BoundaryGauge.center G)

pathIndependenceAt
  : ∀ {ℓC ℓB ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓB}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → (c : Context)
  → {x y : Carrier}
  → BoundaryGauge.closeAt G c x
  → BoundaryGauge.closeAt G c y
  → BoundaryGauge._≈At_ G c x y
pathIndependenceAt G c x≈m y≈m =
  BoundaryGauge.transAt G x≈m (BoundaryGauge.symAt G y≈m)

noForkAt
  : ∀ {ℓC ℓB ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓB}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → Contractive G
  → (c : Context)
  → {x y : Carrier}
  → BoundaryGauge._≈At_ G c x y
noForkAt G C c {x} {y} =
  pathIndependenceAt G c
    (Contractive.contractAt C c x)
    (Contractive.contractAt C c y)

-- Bridge: a contractive boundary gauge gives an indexed contractible fiber.
--
-- This lets you reuse the generic centering/acyclicity theorem surfaces.
boundaryGaugeFiber
  : ∀ {ℓC ℓB ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓB}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : BoundaryGauge {ℓC} {ℓB} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → Contractive G
  → Centering.IndexedContractibleFiber Context Carrier (BoundaryGauge._≈At_ G)
boundaryGaugeFiber G C =
  Centering.mkIndexedContractibleFiber
    (BoundaryGauge.symAt G)
    (BoundaryGauge.transAt G)
    (BoundaryGauge.center G)
    (λ c x → Contractive.contractAt C c x)
