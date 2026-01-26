{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Strengthenings where

-- Index module: optional law layers and “upgrade bundles” that recover standard
-- math strength from the minimal LogOS interfaces.
--
-- This keeps the core interfaces weak (preorders/lax laws), but makes the
-- strengthenings discoverable and easy to import.

open import LogOS.Prelude public

module Orders where
  open import LogOS.Minimal.Con public
  open import LogOS.Minimal.Con.Iso public

module Worlds where
  open import LogOS.Minimal.WorldLaws public

module Closure where
  open import LogOS.Minimal.Closure public
  open import LogOS.Theorems.Reflection.Projector public renaming (idemp≡ to projector-idemp≡)
  open import LogOS.Theorems.Modal.S4 public renaming (idemp≡ to S4-idemp≡)

module Adjunctions where
  open import LogOS.Minimal.Adjunction public
  open import LogOS.Theorems.CategoryTheory.AdjunctionMonads public
  open import LogOS.Theorems.CategoryTheory.BeckChevalley public

module Truth where
  open import LogOS.Minimal.Truth public

module Categories where
  open import LogOS.Minimal.Thin2Cat public

module OmegaSup where
  -- Optional ω-sup selection interfaces used by μ-induction and limit reasoning.
  open import LogOS.Axioms.OmegaSup.Interface public

module Stabilisation where
  -- Domain-theoretic glue for “limit/stabilised” reasoning (μ / ωCPO / transport).
  open import LogOS.Theorems.Boundary.Stabilisation public

module Computation where
  -- Optional limit semantics for processes (μ on slices + μ-fusion transport).
  open import LogOS.Computation.ProcessLimit public

module Guards where
  open import LogOS.Theorems.Meta.Guards public
  open import LogOS.Theorems.Meta.Guards.ObserverCore public
  open import LogOS.Theorems.Meta.Guards.Ports public
  open import LogOS.Theorems.Meta.Guards.HLayer public
