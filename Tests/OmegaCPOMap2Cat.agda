{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.OmegaCPOMap2Cat where

-- Smoke test: the ωCPO + ω-continuous-map spine really forms a locally
-- preordered 2-category (thin 2-cat) with the intended notion of 2-cells.

open import LogOS.Prelude
open import LogOS.Minimal.Con using (ConPreorder; _≈CP_)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Thin2Cat using (Thin2CatLaws)

import LogOS.Theorems.Boundary.OmegaCPOMap2Cat as Ω2
import LogOS.Theorems.CategoryTheory.OmegaCPO2Cat as ΩCT

-- A tiny concrete ωCPO object: the one-element preorder.
--
-- This keeps the test lightweight: we only want to typecheck the 2-cat
-- bookkeeping, not build a rich domain model here.

CP⊤ : ConPreorder lzero
CP⊤ =
  record
    { Con   = ⊤ {ℓ = lzero}
    ; _⊑_   = λ _ _ → ⊤ {ℓ = lzero}
    ; refl  = tt
    ; trans = λ _ _ → tt
    }

ω⊤ : Truth.GuardedCore.OmegaCPO CP⊤
ω⊤ =
  record
    { ⊥     = tt
    ; isBot = λ _ → tt
    ; supω  = λ _ → tt
    ; ub    = λ _ _ → tt
    ; least = λ _ _ _ → tt
    }

module Ω = Ω2.For {ℓ = lzero}
module ΩW = ΩCT.For {ℓ = lzero}

A : Ω.ΩObj
A =
  record
    { CP = CP⊤
    ; ω  = ω⊤
    }

-- The laws are generic, but we also pin them to a concrete object to ensure
-- universe levels/projections line up in practice.

laws : Thin2CatLaws Ω.OmegaCPOThin2Cat
laws = Ω.OmegaCPOThin2CatLaws

-- Also available as a refinement 2-category core.
core : _
core = ΩW.OmegaCPORef2CatCore

-- Sanity: left identity holds as mutual refinement in the hom-preorder.

id-left-≈
  : _≈CP_ (Ω.ΩMapPreorder A A)
          (Ω._∘Ω_ (Ω.idΩMap {A = A}) (Ω.idΩMap {A = A}))
          (Ω.idΩMap {A = A})
id-left-≈ = Thin2CatLaws.id-left laws (Ω.idΩMap {A = A})
