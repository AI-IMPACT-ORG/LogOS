{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.All where

-- ZFC pack: worked ZF/ZFC surfaces living on top of the kernel.
--
-- Canonical pack-first entrypoint:
-- `open import LogOS.Packs.ZFC.All as ZFC`

open import LogOS.API.Minimal public

module SetTheory where
  open import LogOS.Domain.SetTheory.DefinablePack public
  open import LogOS.Domain.SetTheory.Dsl public
  open import LogOS.Domain.SetTheory.FormulaPack public
  open import LogOS.Domain.SetTheory.FormulaFromDefinable public
  open import LogOS.Domain.SetTheory.FormulaDerived public
  open import LogOS.Domain.SetTheory.FullUpgradeFromDefinable public
  open import LogOS.Domain.SetTheory.Pack public
  open import LogOS.Domain.SetTheory.LimitPack public
  open import LogOS.Domain.SetTheory.Cumulative public

module Logic where
  open import LogOS.Logic.FOL.All public
  open import LogOS.Logic.ZFC.All public

import LogOS.Packs.ZFC.WFGraph as WFGraphₜ
module WFGraph = WFGraphₜ

-- Default pack quartet: ZFC via the WFGraph route (full schemata + explicit AC witness).
open WFGraph.WithChoice public
