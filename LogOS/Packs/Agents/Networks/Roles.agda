{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Roles where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.World
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.MultiIO using (MultiBoundaryIO)

-- Role-indexed observational equivalence induced by a `MultiBoundaryIO`.

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
  _≈∂[_]_ r c d = Prop.ObsEqOn (MultiBoundaryIO.Sat∂ M r) c d
