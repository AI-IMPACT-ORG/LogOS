{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.All where

import LogOS.Theorems.Meta.Assumptions as Assumptionsₜ
import LogOS.Theorems.Meta.Base as Baseₜ
import LogOS.Theorems.Meta.Full as Fullₜ
import LogOS.Theorems.Meta.Tarski as Tarskiₜ
import LogOS.Theorems.Meta.Godel as Godelₜ
import LogOS.Theorems.Meta.Lob as Lobₜ
import LogOS.Theorems.Meta.LobCore as LobCoreₜ
import LogOS.Theorems.Meta.Rice as Riceₜ
import LogOS.Theorems.Meta.NoOmniscience as NoOmniscienceₜ
import LogOS.Theorems.Meta.Flow as Flowₜ
import LogOS.Theorems.Meta.FlowCurvature as FlowCurvatureₜ
import LogOS.Theorems.Meta.Diagonal as Diagonalₜ
import LogOS.Theorems.Meta.Kleene2 as Kleene2ₜ
import LogOS.Theorems.Meta.TruthLemma as TruthLemmaₜ
import LogOS.Theorems.Meta.Views as Viewsₜ
import LogOS.Theorems.Meta.CommunicableTruth as CommunicableTruthₜ
import LogOS.Theorems.Meta.MathTruth as MathTruthₜ
import LogOS.Theorems.Meta.MathPhysSynthesis as MathPhysSynthesisₜ
import LogOS.Theorems.Meta.GRHBridge as GRHBridgeₜ
import LogOS.Theorems.Meta.Landauer as Landauerₜ
import LogOS.Theorems.Meta.LandauerIO as LandauerIOₜ
import LogOS.Theorems.Meta.ObserverCore as ObserverCoreₜ
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObserverFromLogicKernelₜ
import LogOS.Theorems.Meta.RefinementSoundness as RefinementSoundnessₜ
import LogOS.Theorems.Meta.TruthPositivity as TruthPositivityₜ
import LogOS.Theorems.Meta.BudgetedTruthPositivity as BudgetedTruthPositivityₜ
import LogOS.Theorems.Meta.LimitPublicisation as LimitPublicisationₜ
import LogOS.Theorems.Meta.SpectralSeparationOutput as SpectralSeparationOutputₜ
import LogOS.Theorems.Meta.BudgetedSeparationOutput as BudgetedSeparationOutputₜ
import LogOS.Theorems.Meta.MonotonePredicates as MonotonePredicatesₜ
import LogOS.Theorems.Meta.Dagger as Daggerₜ
import LogOS.Theorems.Meta.CQM as CQMₜ
import LogOS.Theorems.Meta.QuartetCore as QuartetCoreₜ

module Assumptions = Assumptionsₜ
module Base = Baseₜ
module Full = Fullₜ
module Tarski = Tarskiₜ
module Godel = Godelₜ
module Lob = Lobₜ
module LobCore = LobCoreₜ
module Rice = Riceₜ
module NoOmniscience = NoOmniscienceₜ
module Flow = Flowₜ
module FlowCurvature = FlowCurvatureₜ
module Diagonal = Diagonalₜ
module Kleene2 = Kleene2ₜ
module TruthLemma = TruthLemmaₜ
module Views = Viewsₜ
module CommunicableTruth = CommunicableTruthₜ
module MathTruth = MathTruthₜ
module MathPhysSynthesis = MathPhysSynthesisₜ
module GRHBridge = GRHBridgeₜ
module Landauer = Landauerₜ
module LandauerIO = LandauerIOₜ
module ObserverCore = ObserverCoreₜ
module ObserverFromLogicKernel = ObserverFromLogicKernelₜ
module RefinementSoundness = RefinementSoundnessₜ
module TruthPositivity = TruthPositivityₜ
module BudgetedTruthPositivity = BudgetedTruthPositivityₜ
module LimitPublicisation = LimitPublicisationₜ
module SpectralSeparationOutput = SpectralSeparationOutputₜ
module BudgetedSeparationOutput = BudgetedSeparationOutputₜ
module MonotonePredicates = MonotonePredicatesₜ
module Dagger = Daggerₜ
module CQM = CQMₜ
module QuartetCore = QuartetCoreₜ
