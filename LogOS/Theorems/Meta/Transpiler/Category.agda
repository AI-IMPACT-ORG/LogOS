{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Transpiler.Category where

-- Transpiler category: ports as objects, adapters as morphisms.
-- This is a lightweight alias over the existing port-category packaging.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.System using (System)

import LogOS.Theorems.CategoryTheory.PortCat as PortCat
open import LogOS.Ports.Semantic.Core using (boundarySatSystemFromIO)

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
    (boundarySatSystemFromIO B)
  open C public using (PortCat-instance)

module ForSystem
  {ℓ : Level}
  {ℓForm : Level}
  (S : System {ℓ = ℓ})
  where

  open System S
  open For {ℓ = ℓ} {ℓForm = ℓForm} {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B public
    using (PortCat-instance)
