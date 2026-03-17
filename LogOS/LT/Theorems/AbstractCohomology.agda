{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.AbstractCohomology where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement-first Cech/acyclicity-pattern wrappers over the centering spine.
--
-- This module is intentionally minimal:
-- it provides a degree-1 acyclicity pattern for any contractible fiber,
-- phrased as the existence of coherent edge witnesses for any cover-indexed
-- family of points.
--
-- Engineering reading:
-- contractibility ⇒ no semantic fork ⇒ glueing coherence at every cover index.

open import LogOS.Prelude
import LogOS.LT.Theorems.Centering as Centering

module FromContractibleFiber
  {ℓA ℓ≈ : Level}
  {A : Set ℓA}
  (_≈_ : A → A → Set ℓ≈)
  (F : Centering.ContractibleFiber A _≈_)
  where

  open Centering.ContractibleFiber F renaming
      ( sym≈ to sym≈K
      ; trans≈ to trans≈K
      ; center to centerK
      ; contract to contractK
      )

  module ForCover
    {ℓI : Level}
    (Index : Set ℓI)
    where

    C0 : Set (ℓI ⊔ ℓA)
    C0 = Index → A

    Potential : C0 → Set (ℓI ⊔ ℓ≈)
    Potential x = (i : Index) → _≈_ (x i) centerK

    C1 : C0 → Set (ℓI ⊔ ℓ≈)
    C1 x = (i j : Index) → _≈_ (x i) (x j)

    d0
      : ∀ {x}
      → Potential x
      → C1 x
    d0 p i j = trans≈K (p i) (sym≈K (p j))

    contractPotential
      : (x : C0)
      → Potential x
    contractPotential x i = contractK (x i)

    contractEdge
      : (x : C0)
      → C1 x
    contractEdge x = d0 (contractPotential x)

    H1Trivial : Set (ℓI ⊔ ℓA ⊔ ℓ≈)
    H1Trivial =
      ∀ (x : C0)
      → Σ (Potential x) (λ p → C1 x)

    contractibleFiber⇒H1Trivial : H1Trivial
    contractibleFiber⇒H1Trivial x =
      contractPotential x , d0 (contractPotential x)

    contractibleFiber⇒acyclic1
      : ∀ (x : C0)
      → C1 x
    contractibleFiber⇒acyclic1 x =
      proj₂ (contractibleFiber⇒H1Trivial x)

module FromIndexedContractibleFiber
  {ℓK ℓA ℓ≈ ℓ≤ : Level}
  {Context : Set ℓK}
  {A : Set ℓA}
  (_≈_ : Context → A → A → Set ℓ≈)
  (_≤Ctx_ : Context → Context → Set ℓ≤)
  (F : Centering.IndexedContractibleFiber Context A _≈_)
  (weakenAt : ∀ {c c'} → _≤Ctx_ c c' → ∀ {x y} → _≈_ c' x y → _≈_ c x y)
  where

  open Centering.IndexedContractibleFiber F renaming
      ( symAt to sym≈K
      ; transAt to trans≈K
      ; center to centerK
      ; contract to contractK
      )

  module ForCover
    {ℓI : Level}
    (Index : Set ℓI)
    where

    C0 : Set (ℓI ⊔ ℓA)
    C0 = Index → A

    Potential : Context → C0 → Set (ℓI ⊔ ℓ≈)
    Potential c x = (i : Index) → _≈_ c (x i) centerK

    C1 : Context → C0 → Set (ℓI ⊔ ℓ≈)
    C1 c x = (i j : Index) → _≈_ c (x i) (x j)

    d0
      : ∀ c {x}
      → Potential c x
      → C1 c x
    d0 c p i j = trans≈K {i = c} (p i) (sym≈K {i = c} (p j))

    contractPotential
      : ∀ c
      → (x : C0)
      → Potential c x
    contractPotential c x i = contractK c (x i)

    contractEdge
      : ∀ c
      → (x : C0)
      → C1 c x
    contractEdge c x = d0 c (contractPotential c x)

    weakenPotential
      : ∀ {c c'}
      → _≤Ctx_ c c'
      → ∀ {x}
      → Potential c' x
      → Potential c x
    weakenPotential cc' p i = weakenAt cc' (p i)

    weakenC1
      : ∀ {c c'}
      → _≤Ctx_ c c'
      → ∀ {x}
      → C1 c' x
      → C1 c x
    weakenC1 cc' e i j = weakenAt cc' (e i j)

    contractEdge-weaken
      : ∀ {c c'}
      → (cc' : _≤Ctx_ c c')
      → (x : C0)
      → C1 c x
    contractEdge-weaken {c} {c'} cc' x =
      weakenC1 cc' (contractEdge c' x)
