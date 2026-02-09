{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

import LogOS.Domain.Opacity.Applications.GRH as GRHₜ

import LogOS.Domain.Opacity.NumberTheory.HP.Interface as HPInterfaceₜ
import LogOS.Domain.Opacity.NumberTheory.HP.Flow as HPFlowₜ
import LogOS.Domain.Opacity.NumberTheory.HP.Opacity as HPOpacityₜ

import LogOS.Domain.Opacity.NumberTheory.LFunction.Core as LFunctionCoreₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann as LFunctionRiemannₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts as LFunctionRiemannFactsₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.Selberg as LFunctionSelbergₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack as LFunctionZerosPackₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.RegulatedPartition as LFunctionRegulatedPartitionₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.PartitionZetaBridge as LFunctionPartitionZetaBridgeₜ
import LogOS.Domain.Opacity.NumberTheory.LFunction.DiagonalTX as LFunctionDiagonalTXₜ

module OpacityCore = Coreₜ
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

module Applications where
  module GRH = GRHₜ

module NumberTheory where
  module HP where
    module Interface = HPInterfaceₜ
    module Flow = HPFlowₜ
    module Opacity = HPOpacityₜ

  module LFunction where
    module Core = LFunctionCoreₜ
    module Riemann = LFunctionRiemannₜ
    module RiemannFacts = LFunctionRiemannFactsₜ
    module Selberg = LFunctionSelbergₜ
    module ZerosPack = LFunctionZerosPackₜ
    module RegulatedPartition = LFunctionRegulatedPartitionₜ
    module PartitionZetaBridge = LFunctionPartitionZetaBridgeₜ
    module DiagonalTX = LFunctionDiagonalTXₜ
