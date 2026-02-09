{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.InfoTheory.Core where

-- Curated, stable information-theory surface (no demos).

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

-- Core facts/bridges (Domain). Keep them namespaced to avoid collisions and to
-- make provenance obvious at call sites.
import LogOS.InfoTheory.Shannon.Facts as ShannonFactsₜ
import LogOS.InfoTheory.ObserverDPI as ObserverDPIₜ

module ShannonFacts = ShannonFactsₜ
module ObserverDPI  = ObserverDPIₜ

-- Expose each strand as its own namespace to avoid the `For`-module name clash.
import LogOS.InfoTheory.Shannon.Core     as ShannonCoreₜ
import LogOS.InfoTheory.Shannon.DPI      as ShannonDPIₜ
import LogOS.InfoTheory.Shannon.Capacity as ShannonCapacityₜ
import LogOS.InfoTheory.Shannon.ThermoRG as ShannonThermoRGₜ

module ShannonCore     = ShannonCoreₜ
module ShannonDPI      = ShannonDPIₜ
module ShannonCapacity = ShannonCapacityₜ
module ShannonThermoRG = ShannonThermoRGₜ
