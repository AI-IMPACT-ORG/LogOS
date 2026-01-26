{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Graph where

open import LogOS.Host.Level using (Level; lsuc)
open import LogOS.Host.Product using (Σ; _,_)

-- A minimal, universe-polymorphic graph datatype expressed purely via a
-- vertex carrier and an adjacency relation.

record Graph {ℓ : Level} : Set (lsuc ℓ) where
  field
    Vertex : Set ℓ
    Edge   : Vertex → Vertex → Set ℓ

open Graph public

-- Neighborhood of a vertex as a dependent pair (target vertex, edge witness).

Neighbors : ∀ {ℓ} → (G : Graph {ℓ}) → Graph.Vertex G → Set ℓ
Neighbors G v = Σ (Graph.Vertex G) (λ w → Graph.Edge G v w)

-- Forget the edge witness and just expose adjacency as a predicate.

adjacentTo : ∀ {ℓ} → (G : Graph {ℓ}) → Graph.Vertex G → Graph.Vertex G → Set ℓ
adjacentTo G v w = Graph.Edge G v w

-- Build a graph directly from an adjacency relation.

fromRelation : ∀ {ℓ} → (V : Set ℓ) → (V → V → Set ℓ) → Graph
fromRelation V rel = record { Vertex = V ; Edge = rel }

-- Membership graphs: treat the adjacency relation as “x is related to y”.

membershipGraph : ∀ {ℓ} → (Carrier : Set ℓ) → (Carrier → Carrier → Set ℓ) → Graph
membershipGraph = fromRelation

