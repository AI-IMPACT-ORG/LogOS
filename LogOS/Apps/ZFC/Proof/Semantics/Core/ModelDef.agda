{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Core.ModelDef where

open import LogOS.Prelude using (Level; lsuc)

import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO

record Model {ℓ : Level} : Set (lsuc ℓ) where
  field
    -- Stack-first model, but with Separation/Replacement assumed only at the
    -- first-order (formula-coded) level.
    --
    -- This keeps the proof layer compatible with models that do *not* provide
    -- Agda-level Separation/Replacement schemata.
    stackFO : TowerFO.ZFCStackFO {ℓ}

  open TowerFO.ZFCStackFO stackFO public
  -- First-order evaluation helpers for the internal universe.
  module FO = TowerFO.ForBase base
  open FO public using (Valuation; extend; evalTerm; evalFormula; FunctionalOnX)
  open FO public using (emptySet; pairSet; unionSet; powersetSet; omegaSet; zeroSet; succSet; succ-spec)

fromStackFO : ∀ {ℓ : Level} → TowerFO.ZFCStackFO {ℓ} → Model {ℓ}
fromStackFO S = record { stackFO = S }
