{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
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
  open import LogOS.Domain.ZFC.SetTheory.DefinablePack public
  open import LogOS.Domain.ZFC.SetTheory.Dsl public
  open import LogOS.Domain.ZFC.SetTheory.FormulaPack public
  open import LogOS.Domain.ZFC.SetTheory.FormulaFromDefinable public
  open import LogOS.Domain.ZFC.SetTheory.FormulaDerived public
  open import LogOS.Domain.ZFC.SetTheory.FullUpgradeFromDefinable public
  open import LogOS.Domain.ZFC.SetTheory.Pack public
  open import LogOS.Domain.ZFC.SetTheory.LimitPack public
  open import LogOS.Domain.ZFC.SetTheory.Cumulative public

module Logic where
  open import LogOS.ObjectLogic.FOL.All public
  open import LogOS.ObjectLogic.ZFC.All public

import LogOS.Packs.ZFC.WFGraph as WFGraphₜ
module WFGraph = WFGraphₜ

-- Default pack quartet: ZFC via the WFGraph route (full schemata + explicit AC witness).
open WFGraph.WithChoice public
