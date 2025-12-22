{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Models.Opacity.Core where

-- Curated, stable opacity/observability surface (no demos).

open import LogOS.Domain.Opacity.Core public
open import LogOS.Domain.Opacity.Meaningfulness public

-- Hard-edged “opacity”/barrier results (strategy theorems, not number theory).
open import LogOS.Theorems.Meta.SpectralSeparationOutput public
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BudgetedSSO
import LogOS.Theorems.Meta.BudgetedTruthPositivity as BudgetedTP
import LogOS.Domain.Opacity.NumberTheory.HP.Opacity as HPₒ
module HPOpacity = HPₒ

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
  import LogOS.Domain.Opacity.AccessibleWeilLimitBridge as AWLB
  import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridge as AWML
  import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable as AWMLS
  import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal as AWMLSC
  import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedger as ZAML
  import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedgerStable as ZAMLS
  import LogOS.Domain.Opacity.ZetaHasseYonedaLedger as ZHY

  module WeilObservablePack       = WP.QuartetObservable
  module WeilWeakCriterionPack    = WC.QuartetWeilWeakCriterion
  module WeilCriterionPack        = WC.QuartetWeilCriterion
  module ZetaAxiomLedgerPack      = ZL.QuartetAxiomLedger

  module AccessibleLedgerRSPack   = AWL.QuartetRS
  module AccessibleLedgerZetaPack = AWL.QuartetZeta

  module AccessibleLimitBridgePack            = AWLB.QuartetLimitBridge
  module AccessibleMeetLimitBridgePack        = AWML.QuartetMeetLimitBridge
  module AccessibleMeetLimitStablePack        = AWMLS.QuartetMeetLimitStable
  module AccessibleMeetLimitStableCofinalPack = AWMLSC.QuartetMeetLimitStableCofinal

  module ZetaMeetLimitLedgerPack        = ZAML.QuartetZetaMeetLimitLedger
  module ZetaMeetLimitLedgerStablePack  = ZAMLS.QuartetZetaMeetLimitLedgerStable
  module ZetaHasseYonedaLedgerPack      = ZHY.QuartetZetaHasseYonedaLedger
