{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.InfoTheory.All where

-- Information theory pack (Shannon + thermo/RG-facing surfaces).

open import LogOS.Packs.Trust using (PackTrust; stable)

packTrust : PackTrust
packTrust = record { level = stable }

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Physics public

module Core where
  open import LogOS.Packs.InfoTheory.Core public

module Applications where
  open import LogOS.Packs.InfoTheory.Applications.All public
