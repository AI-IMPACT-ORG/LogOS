{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.FirstProof.Experimental.All where

-- FirstProof challenge scaffold pack (sketch territory; intentionally scaffold-level).

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.FirstProof.Experimental.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

module Core where
  open import LogOS.Packs.FirstProof.Experimental.Core public
