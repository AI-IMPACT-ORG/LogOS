{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.All where

-- Computational universality pack (UniversalIR-first):
-- - UniversalIR core + multi-paradigm agreement
-- - a meta-language refinement (schemes/processes + functorial contracts)

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.Universality.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Universality public

module UniversalIR where
  -- Re-export the full UniversalIR pack (umbrella).
  open import LogOS.Packs.UniversalIR.All public

module MetaLanguage where
  open import LogOS.MetaLanguage.All public

module Core where
  open import LogOS.Packs.Universality.Core public

module Applications where
  open import LogOS.Packs.Universality.Applications.All public

module VacuityGuards where
  open import LogOS.Packs.Universality.VacuityGuards public

-- Common discoverability alias: “meaningfulness” here is “non-vacuity”.
module Meaningfulness = VacuityGuards
