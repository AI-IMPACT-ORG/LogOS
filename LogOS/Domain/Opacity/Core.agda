{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Core where

-- Core module index for the Opacity strand.
--
-- Design intent:
-- - Theorems here are conditional: analytic/physical content is always explicit in record fields.
-- - This strand is application-agnostic: concrete targets (e.g. GRH) are exported separately.
-- - Keep application-facing wrappers out of the core surface; expose them under
--   `LogOS.Domain.Opacity.Applications.*`.

-- Note: we intentionally avoid `open import … public` re-exports here.
-- Instead, we expose a namespaced index so the provenance of each definition
-- is visible at use sites (and the “math objects” pop).

import LogOS.Domain.Opacity.Meaningfulness as Meaningfulnessₜ
import LogOS.Domain.Opacity.WeilPositivityBridge as WeilPositivityBridgeₜ
import LogOS.Domain.Opacity.WeilCriterionLedger as WeilCriterionLedgerₜ
import LogOS.Domain.Opacity.WeilCriterionDagger as WeilCriterionDaggerₜ
import LogOS.Domain.Opacity.ZetaTruthLedger as ZetaTruthLedgerₜ
import LogOS.Domain.Opacity.ObservableSector as ObservableSectorₜ

import LogOS.Domain.Opacity.WeilProbeImplication as WeilProbeImplicationₜ
import LogOS.Domain.Opacity.AccessibleWeilLedger as AccessibleWeilLedgerₜ
import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStable as AccessibleWeilMeetLimitBridgeStableₜ
import LogOS.Domain.Opacity.AccessibleWeilMeetLimitBridgeStableCofinal as AccessibleWeilMeetLimitBridgeStableCofinalₜ
import LogOS.Domain.Opacity.ZetaAccessibleMeetLimitLedgerStable as ZetaAccessibleMeetLimitLedgerStableₜ

import LogOS.Domain.Opacity.HasseObservableClass as HasseObservableClassₜ
import LogOS.Domain.Opacity.HasseYonedaTransport as HasseYonedaTransportₜ
import LogOS.Domain.Opacity.ZetaHasseYonedaLedger as ZetaHasseYonedaLedgerₜ

import LogOS.Domain.Opacity.LogicLanglands as LogicLanglandsₜ
import LogOS.Domain.Opacity.TruthSeparation as TruthSeparationₜ

module Meaningfulness = Meaningfulnessₜ

module WeilPositivityBridge = WeilPositivityBridgeₜ
module WeilCriterionLedger = WeilCriterionLedgerₜ
module WeilCriterionDagger = WeilCriterionDaggerₜ
module ZetaTruthLedger = ZetaTruthLedgerₜ
module ObservableSector = ObservableSectorₜ

module WeilProbeImplication = WeilProbeImplicationₜ
module AccessibleWeilLedger = AccessibleWeilLedgerₜ
module AccessibleWeilMeetLimitBridgeStable = AccessibleWeilMeetLimitBridgeStableₜ
module AccessibleWeilMeetLimitBridgeStableCofinal = AccessibleWeilMeetLimitBridgeStableCofinalₜ
module ZetaAccessibleMeetLimitLedgerStable = ZetaAccessibleMeetLimitLedgerStableₜ

module HasseObservableClass = HasseObservableClassₜ
module HasseYonedaTransport = HasseYonedaTransportₜ
module ZetaHasseYonedaLedger = ZetaHasseYonedaLedgerₜ

module LogicLanglands = LogicLanglandsₜ
module TruthSeparation = TruthSeparationₜ
