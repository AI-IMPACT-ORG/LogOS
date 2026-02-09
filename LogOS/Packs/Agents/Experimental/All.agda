{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.All where

-- Experimental surface: stable agents pack plus transformer/scaling and
-- complexity-linked physics/RG-flow extensions.

open import LogOS.Packs.Trust using (PackTrust; experimental)

packTrust : PackTrust
packTrust = record { level = experimental }

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Universality public
  open import LogOS.Packs.Assumptions.Physics public

module Core where
  open import LogOS.Packs.Agents.Core public

module Lab where
  open import LogOS.Packs.Agents.Lab.All public
  import LogOS.Packs.Agents.Experimental.Lab as ExperimentalLab

  module ExperimentalArguments = ExperimentalLab.Arguments
  module ExperimentalCore = ExperimentalLab.Core
  module ExperimentalPhysics = ExperimentalLab.Physics
  module ExperimentalCapstone = ExperimentalLab.Capstone

  module ExperimentalEmit = ExperimentalLab.Emit
  module ExperimentalLearning = ExperimentalLab.Learning
  module ExperimentalSafety = ExperimentalLab.Safety
  module ExperimentalFrameworks = ExperimentalLab.Frameworks
  module ExperimentalComparisons = ExperimentalLab.Comparisons
  module ExperimentalExamples = ExperimentalLab.Examples

module Applications where
  open import LogOS.Packs.Agents.Applications.All public

module Arguments where
  open import LogOS.Packs.Agents.Experimental.Arguments.All public

module Learning where
  module RGFlow where
    open import LogOS.Packs.Agents.Experimental.Learning.RGFlow public

module Physics where
  open import LogOS.Packs.Agents.Experimental.Physics.All public

module Safety where
  module NoTotalAuditor where
    open import LogOS.Packs.Agents.Experimental.Safety.NoTotalAuditor public
