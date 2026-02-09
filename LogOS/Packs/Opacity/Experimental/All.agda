{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Opacity.Experimental.All where

-- Opacity pack (experimental):
-- - kernel-level opacity infrastructure
-- - conditional application ledger (guarded)

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.Opacity.Experimental.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

module AssumptionBundles where
  open import LogOS.Packs.Assumptions.ZFC public

module Opacity where
  open import LogOS.Packs.Opacity.Experimental.Core public

-- Common discoverability alias: “meaningfulness” = explicit vacuity guards.
module Meaningfulness = Opacity.Meaningfulness

module Applications where
  open import LogOS.Packs.Opacity.Experimental.Applications.All public
