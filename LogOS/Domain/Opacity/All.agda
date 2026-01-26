{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.All where

-- Index module for the Opacity domain (discoverability only).

import LogOS.Domain.Opacity.Core as Coreₜ
import LogOS.Domain.Opacity.Meaningfulness as Meaningfulnessₜ
import LogOS.Domain.Opacity.GRHLedger as GRHLedgerₜ
import LogOS.Domain.Opacity.GRH_Vacuity_Guards as GRH_Vacuity_Guardsₜ
import LogOS.Domain.Opacity.AccessibleWeilLedger as AccessibleWeilLedgerₜ
import LogOS.Domain.Opacity.WeilCriterionLedger as WeilCriterionLedgerₜ
import LogOS.Domain.Opacity.WeilPositivityBridge as WeilPositivityBridgeₜ
import LogOS.Domain.Opacity.PNTBridge as PNTBridgeₜ
import LogOS.Domain.Opacity.TruthSeparation as TruthSeparationₜ
import LogOS.Domain.Opacity.TruthSeparationForcing as TruthSeparationForcingₜ
import LogOS.Domain.Opacity.LogicLanglands as LogicLanglandsₜ

import LogOS.Domain.Opacity.Applications.All as Applicationsₜ
import LogOS.Domain.Opacity.NumberTheory.All as NumberTheoryₜ

module Core = Coreₜ
module Meaningfulness = Meaningfulnessₜ
module GRHLedger = GRHLedgerₜ
module GRH_Vacuity_Guards = GRH_Vacuity_Guardsₜ
module AccessibleWeilLedger = AccessibleWeilLedgerₜ
module WeilCriterionLedger = WeilCriterionLedgerₜ
module WeilPositivityBridge = WeilPositivityBridgeₜ
module PNTBridge = PNTBridgeₜ
module TruthSeparation = TruthSeparationₜ
module TruthSeparationForcing = TruthSeparationForcingₜ
module LogicLanglands = LogicLanglandsₜ

module Applications = Applicationsₜ
module NumberTheory = NumberTheoryₜ
