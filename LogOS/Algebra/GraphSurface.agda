{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.GraphSurface where

open import LogOS.Prelude

open import LogOS.Algebra.Ring
open import LogOS.Algebra.FiniteGraph
open import LogOS.Prelude.Graph

-- Some algebraic models (Ihara, spectral GRH) package graphs as adjacency
-- matrices over a ring. To reuse the canonical Graph datatype we expose a tiny
-- surface where the model supplies an adjacency predicate; we immediately
-- derive a Graph witness for downstream code.

record FiniteGraphSurface {ℓ : Level}
                          (R : Ring {ℓ})
                          (G : FiniteGraph R)
                          : Set (lsuc ℓ) where
  field
    adjacency : FiniteGraph.V G → FiniteGraph.V G → Set ℓ

  toGraph : Graph
  toGraph = membershipGraph (FiniteGraph.V G) adjacency

open FiniteGraphSurface public
