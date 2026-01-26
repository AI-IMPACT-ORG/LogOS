{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Opacity.Experimental.Core where

-- Curated, experimental opacity/observability surface (no demos).

open import LogOS.Packs.Trust using (PackTrust; experimental)

packTrust : PackTrust
packTrust = record { level = experimental }

-- Philosophy: keep this surface namespaced (module-index style). If you want a
-- large umbrella import, use `LogOS.Packs.Opacity.Experimental.All`.

import LogOS.Domain.Opacity.Core as Domainₜ
module Domain = Domainₜ

import LogOS.Domain.Opacity.TelemetryInvariant as TelemetryInvariantₜ
module TelemetryInvariant = TelemetryInvariantₜ

import LogOS.Domain.Opacity.Indistinguishability as Indistinguishabilityₜ
module Indistinguishability = Indistinguishabilityₜ

-- Meaningfulness/vacuity guards (export the canonical name directly).
module Meaningfulness = Domain.Meaningfulness
open Meaningfulness public using (VacuityGuards)

-- Hard-edged “opacity”/barrier results (strategy theorems, not number theory).
import LogOS.Theorems.Meta.SpectralSeparationOutput as SpectralSeparationOutputₜ
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BudgetedSSO
import LogOS.Theorems.Meta.BudgetedTruthPositivity as BudgetedTP
import LogOS.Domain.Opacity.NumberTheory.HP.Opacity as HPₒ
module HPOpacity = HPₒ

module SpectralSeparationOutput = SpectralSeparationOutputₜ
module BudgetedSeparationOutput = BudgetedSSO
module BudgetedTruthPositivity = BudgetedTP

-- Compatibility alias (explicit guards).
import LogOS.Domain.Opacity.GRH_Vacuity_Guards as GRH_Vacuity_Guardsₜ
module GRH_Vacuity_Guards = GRH_Vacuity_Guardsₜ

-- --------------------------------------------------------------------------
-- Pack skeleton entrypoints (uniform API).
--
-- The Opacity strand is intentionally split across several “ledger/bridge”
-- modules. To make the `Assumptions/Claim/Pack/mkPack` quartet operational
-- without polluting the top-level namespace (and risking collisions), we group
-- the key entrypoints here.

module Packs where
  import LogOS.Domain.Opacity.WeilPositivityBridge as WP
  import LogOS.Domain.Opacity.WeilCriterionLedger as WC
  import LogOS.Domain.Opacity.ZetaTruthLedger as ZL

  import LogOS.Domain.Opacity.AccessibleWeilLedger as AWL
  import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable as AWMLS
  import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal as AWMLSC
  import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedgerStable as ZAMLS
  import LogOS.Domain.Opacity.ZetaHasseYonedaLedger as ZHY

  module WeilObservablePack       = WP.QuartetObservable
  module WeilWeakCriterionPack    = WC.QuartetWeilWeakCriterion
  module WeilCriterionPack        = WC.QuartetWeilCriterion
  module ZetaAxiomLedgerPack      = ZL.QuartetAxiomLedger

  module AccessibleLedgerRSPack   = AWL.QuartetRS
  module AccessibleLedgerZetaPack = AWL.QuartetZeta

  module AccessibleLedgerRSStableTruthPack   = AWL.QuartetRSStableTruth
  module AccessibleLedgerZetaStableTruthPack = AWL.QuartetZetaStableTruth

  module AccessibleMeetLimitStablePack        = AWMLS.QuartetMeetLimitStable
  module AccessibleMeetLimitStableCofinalPack = AWMLSC.QuartetMeetLimitStableCofinal

  module ZetaMeetLimitLedgerStablePack  = ZAMLS.QuartetZetaMeetLimitLedgerStable
  module ZetaHasseYonedaLedgerPack      = ZHY.QuartetZetaHasseYonedaLedger
