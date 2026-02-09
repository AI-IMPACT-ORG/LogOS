{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Showcase.FutamuraDiagonal where

-- A small, documentation-oriented surface that puts two classic “self-reference”
-- artifacts next to each other:
-- - Futamura projections (staging / partial evaluation),
-- - Lawvere-style diagonal / diagonal lemma packs.
--
-- This is *not* a stable pack surface; it intentionally re-exports meta-theorem
-- assumption modules. Use it for the docs and for experimentation.

open import LogOS.Prelude public

-- Futamura (UniversalIR): scheme-level Futamura-1 + assumption-scoped code-level story.
open import LogOS.UniversalIR.Futamura public

-- Diagonalisation / self-reference packs (assumption-scoped).
import LogOS.Theorems.Meta.Assumptions.Diagonal as Diagonalₜ
module Diagonal = Diagonalₜ

-- Presentation-independence currency used by the docs’ narrative (ports/adapters + bootstrapping).
import LogOS.Theorems.Meta.Bootstrapping as Bootstrappingₜ
module Bootstrapping = Bootstrappingₜ

import LogOS.Ports.Semantic.Interoperability as Interoperabilityₜ
module Interoperability = Interoperabilityₜ

import LogOS.Ports.Semantic.Interlingua as Interlinguaₜ
module Interlingua = Interlinguaₜ

import LogOS.Ports.Semantic.SatSystemIO as SatSystemIOₜ
module SatSystemIO = SatSystemIOₜ

import LogOS.Packs.Showcase.FutamuraDiagonalSpine as Spineₜ
module Spine = Spineₜ
