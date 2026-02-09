{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PortSpineOnly where

-- Regression: the “ports/adapters spine” should be usable port-first.
--
-- In particular, downstream developments should be able to import the
-- architecture map and work with boundary ports + interlingua translations
-- without touching kernel internals.

open import LogOS.Prelude

import LogOS.Minimal.Truth as Truth

open import LogOS.API.Architecture as Architecture
open Architecture.Downstream

import LogOS.Ports.Semantic.Interlingua as Interlingua

module _
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  {W   : Worlds.WorldH Sig Q}
  {BB  : BulkBoundary ℓ}
  {H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B   : BoundaryIO Sig Q W BB H)
  {ℓForm₁ ℓForm₂ : Level}
  (P₁  : BoundaryPort {ℓForm = ℓForm₁} Sig Q W BB H B)
  (P₂  : BoundaryPort {ℓForm = ℓForm₂} Sig Q W BB H B)
  where

  module I = Interlingua.For B P₁ P₂

  -- Smoke: the bundled endomap interface plugs into the interlingua naturality lemma.
  useObsEndo = I.ported-closure-naturality-ObsEndo
