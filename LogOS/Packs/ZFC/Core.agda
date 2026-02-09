{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.Core where

-- Curated, stable ZF/ZFC surface (namespaced index).
--
-- Philosophy: `Core` is intentionally *minimal* and namespaced.
-- - Use `LogOS.Packs.ZFC.All` as the umbrella import.
-- - Use `LogOS.Packs.ZFC.Surface` as the “stable lock” entrypoint.
-- - Use `LogOS.Packs.ZFC.Applications.*` for story-level wrappers.

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

-- Domain-level set theory (kernel-facing) surfaces.
import LogOS.ZFC.SetTheory.DefinablePack         as DefinablePackₜ
import LogOS.ZFC.SetTheory.Dsl                   as Dslₜ
import LogOS.ZFC.SetTheory.ForcingInvariant      as ForcingInvariantₜ
import LogOS.ZFC.SetTheory.FormulaPack           as FormulaPackₜ
import LogOS.ZFC.SetTheory.FormulaFromDefinable  as FormulaFromDefinableₜ
import LogOS.ZFC.SetTheory.FormulaDerived        as FormulaDerivedₜ
import LogOS.ZFC.SetTheory.FullUpgradeFromDefinable as FullUpgradeFromDefinableₜ
import LogOS.ZFC.SetTheory.Pack                  as Packₜ
import LogOS.ZFC.SetTheory.LimitPack             as LimitPackₜ
import LogOS.ZFC.SetTheory.Cumulative            as Cumulativeₜ
import LogOS.ZFC.SetTheory.SchemaTheorems        as SchemaTheoremsₜ

module SetTheory where
  module DefinablePack = DefinablePackₜ
  module Dsl = Dslₜ
  module ForcingInvariant = ForcingInvariantₜ
  module FormulaPack = FormulaPackₜ
  module FormulaFromDefinable = FormulaFromDefinableₜ
  module FormulaDerived = FormulaDerivedₜ
  module FullUpgradeFromDefinable = FullUpgradeFromDefinableₜ
  module Pack = Packₜ
  module LimitPack = LimitPackₜ
  module Cumulative = Cumulativeₜ
  module SchemaTheorems = SchemaTheoremsₜ

-- Proof-theoretic façades (FOL + ZFC object logic).
module Logic where
  import LogOS.ObjectLogic.FOL.All as FOLₜ
  import LogOS.ObjectLogic.ZFC.All as ZFCₜ
  module FOL = FOLₜ
  module ZFC = ZFCₜ

  module ClassicalFOL where
    import LogOS.ObjectLogic.FOL.AllClassical as ClassicalFOLₜ
    module Bundle = ClassicalFOLₜ

-- The canonical WFGraph route (worked pack skeleton, models, and upgrades).
import LogOS.Packs.ZFC.WFGraph as WFGraphₜ
module WFGraph = WFGraphₜ

