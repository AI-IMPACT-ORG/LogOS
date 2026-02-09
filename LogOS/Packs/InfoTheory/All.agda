{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.InfoTheory.All where

-- Information theory pack (Shannon + thermo/RG-facing surfaces).

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.InfoTheory.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.Physics public

module Core where
  open import LogOS.Packs.InfoTheory.Core public

module Applications where
  open import LogOS.Packs.InfoTheory.Applications.All public
