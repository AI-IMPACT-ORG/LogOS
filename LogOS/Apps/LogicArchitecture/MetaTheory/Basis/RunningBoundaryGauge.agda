{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.RunningBoundaryGauge where

-- MetaTheory — “Running center” context gauge (EFT-style approximation).
--
-- This generalises `LogOS.LT.Theorems.BoundaryGauge` by allowing the
-- distinguished center to depend on context (the “running” effective model).
--
-- Because the center itself varies with context, the canonical theorem shape
-- here is pointwise contractibility/no-fork at each context, not a single
-- indexed contractible fiber with one global center.

open import LogOS.Prelude
import LogOS.LT.Theorems.Centering as Centering

record RunningBoundaryGauge
  {ℓC ℓK ℓ≤ ℓ≈ : Level}
  (Carrier : Set ℓC)
  (Context : Set ℓK)
  (_≤Ctx_ : Context → Context → Set ℓ≤)
  : Set (lsuc (ℓC ⊔ ℓK ⊔ ℓ≤ ⊔ ℓ≈)) where
  infix 4 _≈At_

  field
    centerAt : Context → Carrier
    _≈At_    : Context → Carrier → Carrier → Set ℓ≈

    symAt
      : ∀ {c x y}
      → _≈At_ c x y
      → _≈At_ c y x

    transAt
      : ∀ {c x y z}
      → _≈At_ c x y
      → _≈At_ c y z
      → _≈At_ c x z

    weakenAt
      : ∀ {c c'}
      → _≤Ctx_ c c'
      → ∀ {x y}
      → _≈At_ c' x y
      → _≈At_ c x y

  closeAt : Context → Carrier → Set ℓ≈
  closeAt c x = _≈At_ c x (centerAt c)

record RunningContractive
  {ℓC ℓK ℓ≤ ℓ≈ : Level}
  {Carrier : Set ℓC}
  {Context : Set ℓK}
  {_≤Ctx_ : Context → Context → Set ℓ≤}
  (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  : Set (lsuc (ℓC ⊔ ℓK ⊔ ℓ≤ ⊔ ℓ≈)) where
  field
    contractAt
      : ∀ (c : Context)
      → (x : Carrier)
      → RunningBoundaryGauge.closeAt G c x

fiberAt
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningContractive G
  → (c : Context)
  → Centering.ContractibleFiber Carrier (RunningBoundaryGauge._≈At_ G c)
fiberAt G C c =
  Centering.mkContractibleFiber
    (λ {x} {y} → RunningBoundaryGauge.symAt G {c = c} {x = x} {y = y})
    (λ {x} {y} {z} →
      RunningBoundaryGauge.transAt G {c = c} {x = x} {y = y} {z = z})
    (RunningBoundaryGauge.centerAt G c)
    (λ x → RunningContractive.contractAt C c x)

runningFiber
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningContractive G
  → (c : Context)
  → Centering.ContractibleFiber Carrier (RunningBoundaryGauge._≈At_ G c)
runningFiber = fiberAt

runningPathIndependence
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningContractive G
  → (c : Context)
  → Centering.PathIndependence (RunningBoundaryGauge._≈At_ G c)
runningPathIndependence G C c =
  Centering.contractible⇒path-independence (runningFiber G C c)

runningNoFork
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningContractive G
  → (c : Context)
  → Centering.NoSemanticFork (RunningBoundaryGauge._≈At_ G c)
runningNoFork G C c =
  Centering.contractible⇒noSemanticFork (runningFiber G C c)

-- EFT-style “matching”: centers at different contexts agree when restricted to
-- the weaker context.
record RunningMatched
  {ℓC ℓK ℓ≤ ℓ≈ : Level}
  {Carrier : Set ℓC}
  {Context : Set ℓK}
  {_≤Ctx_ : Context → Context → Set ℓ≤}
  (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  : Set (lsuc (ℓC ⊔ ℓK ⊔ ℓ≤ ⊔ ℓ≈)) where
  field
    matchCenters
      : ∀ {c c'}
      → _≤Ctx_ c c'
      → RunningBoundaryGauge._≈At_ G c
          (RunningBoundaryGauge.centerAt G c')
          (RunningBoundaryGauge.centerAt G c)

closeAt-weaken
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningMatched G
  → ∀ {c c'}
  → _≤Ctx_ c c'
  → ∀ {x}
  → RunningBoundaryGauge.closeAt G c' x
  → RunningBoundaryGauge.closeAt G c x
closeAt-weaken G M cc' x≈m' =
  RunningBoundaryGauge.transAt G
    (RunningBoundaryGauge.weakenAt G cc' x≈m')
    (RunningMatched.matchCenters M cc')

runningMatch
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningMatched G
  → ∀ {c c'}
  → _≤Ctx_ c c'
  → RunningBoundaryGauge._≈At_ G c
      (RunningBoundaryGauge.centerAt G c')
      (RunningBoundaryGauge.centerAt G c)
runningMatch _ M = RunningMatched.matchCenters M

pathIndependenceAt
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningContractive G
  → (c : Context)
  → {x y : Carrier}
  → RunningBoundaryGauge.closeAt G c x
  → RunningBoundaryGauge.closeAt G c y
  → RunningBoundaryGauge._≈At_ G c x y
pathIndependenceAt G C c _ _ =
  runningPathIndependence G C c

noForkAt
  : ∀ {ℓC ℓK ℓ≤ ℓ≈}
    {Carrier : Set ℓC}
    {Context : Set ℓK}
    {_≤Ctx_ : Context → Context → Set ℓ≤}
    (G : RunningBoundaryGauge {ℓC} {ℓK} {ℓ≤} {ℓ≈} Carrier Context _≤Ctx_)
  → RunningContractive G
  → (c : Context)
  → {x y : Carrier}
  → RunningBoundaryGauge._≈At_ G c x y
noForkAt G C c = runningNoFork G C c
