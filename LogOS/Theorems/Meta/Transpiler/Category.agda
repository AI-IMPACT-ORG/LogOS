{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Transpiler.Category where

-- Transpiler category: ports as objects, adapters as morphisms.
-- This is a thin alias over the existing port-category packaging.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)

import LogOS.Theorems.CategoryTheory.PortCat as PortCat

module For
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  where

  open LogOSSignature Sig
  open BulkBoundary BB
  module C = PortCat.For
    {ℓCtx = ℓ} {ℓCon = ℓ} {ℓSat = ℓ} {ℓForm = ℓForm}
    {Ctx = ∂Cosp} {Con = Con_bnd}
    (BoundaryIO.Sat∂ B)
  open C public using (PortCat-instance)
