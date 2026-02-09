{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Universality.All where

-- Index module for the Universality topic library (discoverability only).
--
-- Prefer curated pack surfaces for downstream use:
-- - Stable pack: `LogOS.Packs.Universality.Surface`
-- - Umbrella: `LogOS.Universality.Surface`

import LogOS.Universality.Comp as Compₜ
import LogOS.Universality.Complexity as Complexityₜ
import LogOS.Universality.ComplexitySpectrum as ComplexitySpectrumₜ
import LogOS.Universality.Core as Coreₜ
import LogOS.Universality.FlowUniversality as FlowUniversalityₜ
import LogOS.Universality.Growth as Growthₜ
import LogOS.Universality.Kernel as Kernelₜ
import LogOS.Universality.KernelRich as KernelRichₜ
import LogOS.Universality.Lemmas as Lemmasₜ
import LogOS.Universality.Models as Modelsₜ
import LogOS.Universality.PAExample as PAExampleₜ
import LogOS.Universality.Physics as Physicsₜ
import LogOS.Universality.SchemePresentation as SchemePresentationₜ
import LogOS.Universality.Separation as Separationₜ
import LogOS.Universality.RiceTransport as RiceTransportₜ
import LogOS.Universality.BodyEqTransport as BodyEqTransportₜ
import LogOS.Universality.Surface as Surfaceₜ

module Comp = Compₜ
module Complexity = Complexityₜ
module ComplexitySpectrum = ComplexitySpectrumₜ
module Core = Coreₜ
module FlowUniversality = FlowUniversalityₜ
module Growth = Growthₜ
module Kernel = Kernelₜ
module KernelRich = KernelRichₜ
module Lemmas = Lemmasₜ
module Models = Modelsₜ
module PAExample = PAExampleₜ
module Physics = Physicsₜ
module SchemePresentation = SchemePresentationₜ
module Separation = Separationₜ
module RiceTransport = RiceTransportₜ
module BodyEqTransport = BodyEqTransportₜ
module Surface = Surfaceₜ
