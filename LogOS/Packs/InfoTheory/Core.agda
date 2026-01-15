{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.InfoTheory.Core where

-- Curated, stable information-theory surface (no demos).

open import LogOS.Domain.InfoTheory.Shannon.Facts public
open import LogOS.Domain.InfoTheory.ObserverDPI public

-- Expose each strand as its own namespace to avoid the `For`-module name clash.
import LogOS.Domain.InfoTheory.Shannon.Core     as ShannonCoreₜ
import LogOS.Domain.InfoTheory.Shannon.DPI      as ShannonDPIₜ
import LogOS.Domain.InfoTheory.Shannon.Capacity as ShannonCapacityₜ
import LogOS.Domain.InfoTheory.Shannon.ThermoRG as ShannonThermoRGₜ

module ShannonCore     = ShannonCoreₜ
module ShannonDPI      = ShannonDPIₜ
module ShannonCapacity = ShannonCapacityₜ
module ShannonThermoRG = ShannonThermoRGₜ
