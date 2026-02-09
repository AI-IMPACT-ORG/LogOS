{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Roles where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
import LogOS.Minimal.View as View
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.World
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.MultiIO using (MultiBoundaryIO)

-- Role-indexed observational equality induced by a `MultiBoundaryIO`.

module For
  {ℓ : Level}
  {Role : Set ℓ}
  {Sig  : LogOSSignature ℓ}
  {Q    : QAdapter ℓ}
  {W    : Worlds.WorldH Sig Q}
  {BB   : BulkBoundary ℓ}
  {H    : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (M    : MultiBoundaryIO Role Sig Q W BB H)
  where

  open BulkBoundary BB using (Con_bnd)

  infix 4 _≈∂[_]_
  _≈∂[_]_ : Role → Con_bnd → Con_bnd → Set ℓ
  _≈∂[_]_ r c d = View.Obs≈ (MultiBoundaryIO.Sat∂ M r) c d

  -- Non-glyph alias (keeps notation consistent with `Obs≈obs` in kernel tiers).
  Obs≈∂ : Role → Con_bnd → Con_bnd → Set ℓ
  Obs≈∂ r c d = _≈∂[_]_ r c d

  -- Presentation alias: pointwise satisfaction equivalence (`↔`).
  ObsEq∂ : Role → Con_bnd → Con_bnd → Set ℓ
  ObsEq∂ r c d = Prop.ObsEqOn (MultiBoundaryIO.Sat∂ M r) c d

  ObsEq∂↔≈∂ : ∀ r {c d} → Prop._↔_ (ObsEq∂ r c d) (_≈∂[_]_ r c d)
  ObsEq∂↔≈∂ r {c} {d} = View.ObsEqOn↔Obs≈ (MultiBoundaryIO.Sat∂ M r) {x = c} {y = d}

  ObsEq∂↔Obs≈∂ : ∀ r {c d} → Prop._↔_ (ObsEq∂ r c d) (Obs≈∂ r c d)
  ObsEq∂↔Obs≈∂ r = ObsEq∂↔≈∂ r
