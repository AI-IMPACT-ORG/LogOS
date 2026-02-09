{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.All where

-- ZFC pack: worked ZF/ZFC surfaces living on top of the kernel.
--
-- Canonical pack-first entrypoint:
-- `open import LogOS.Packs.ZFC.All as ZFC`

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.ZFC.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

module Core where
  open import LogOS.Packs.ZFC.Core public

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.ZFC public

module Applications where
  open import LogOS.Packs.ZFC.Applications.All public

module VacuityGuards where
  open import LogOS.Packs.ZFC.VacuityGuards public

module Examples where
  open import LogOS.Packs.ZFC.Examples public

-- Common discoverability alias: “meaningfulness” here is “non-vacuity”.
module Meaningfulness = VacuityGuards

module WFGraph where
  open import LogOS.Packs.ZFC.WFGraph public

-- Default pack quartet: ZFC via the WFGraph route (full schemata + explicit AC witness).
module Default = WFGraph.WithChoice
