{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.Supplementary.HF.HFGraph where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Domain.ZFC.Supplementary.HF.HFFragment as HF
open import LogOS.Prelude.Graph

-- View the hereditarily-finite universe as a graph: vertices are HF sets and
-- there is a directed edge x → y precisely when x ∈ y. This graph exposes the
-- “set as graph” intuition used by the canonical rewriting model and lets
-- downstream code reason uniformly about combinatorics and membership.

HFGraph : Graph
HFGraph = membershipGraph HF.HF HF._∈HF_

edge→membership : ∀ {x y} → Edge HFGraph x y → x HF.∈HF y
edge→membership = λ p → p

membership→edge : ∀ {x y} → x HF.∈HF y → Edge HFGraph x y
membership→edge = λ p → p

open Graph HFGraph renaming (Vertex to HFVertex) public

HF-neighbors : HF.HF → Set
HF-neighbors = Neighbors HFGraph

HF-edge-respects≈ :
  ∀ {x y y'} → Edge HFGraph x y → y HF.≈HF y' → Edge HFGraph x y'
HF-edge-respects≈ {x} {y} {y'} edge y≈y' =
  let swap = HF.mem-ext-HF y≈y' x
  in Prop._↔_.to swap edge
