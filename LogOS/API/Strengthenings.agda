{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
--
-- This surface is for:
-- - optional upgrade bundles (μ-limit transport, stronger closure/adjunction laws, ω-sup interfaces)
--
-- Not for:
-- - minimal safe core work (use `LogOS.API.Minimal`)
-- - hiding axiom usage: axiom interfaces live under `LogOS.API.Axioms` and are explicit.

open import LogOS.Prelude public

import LogOS.API.Axioms as Axioms

module Orders where
  open import LogOS.Minimal.Con public
  open import LogOS.Minimal.Con.Iso public

module Worlds where
  open import LogOS.Minimal.WorldLaws public

module Closure where
  open import LogOS.Minimal.Closure public

  -- Re-export the specific idempotence witnesses without pulling the full
  -- theorem modules into this surface.
  import LogOS.Theorems.Reflection.Projector as Projector
  import LogOS.Theorems.Modal.S4 as S4

  projector-idemp≡ = Projector.idemp≡
  S4-idemp≡ = S4.idemp≡

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
  open Axioms.OmegaSup public

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
