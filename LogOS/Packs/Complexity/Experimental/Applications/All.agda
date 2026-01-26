{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Experimental.Applications.All where

-- Curated “application” entrypoints for the experimental Complexity storyline.
--
-- This namespace exists to make the repo’s “applications as model-theoretic
-- packs” structure explicit and uniform across domains.

module Models where
  import LogOS.Domain.Complexity.Model as Model

module Examples where
  -- NOTE: Kept lightweight for fast typechecking. Import examples directly:
  -- - `LogOS.Domain.Complexity.Examples.GoldenPath`
  -- - `LogOS.Domain.Complexity.Examples.InfoRouteChain`

module PvsNP where
  open import LogOS.Packs.Complexity.Experimental.PvsNP.Public public
  open import LogOS.Domain.Complexity.PvsNPLedger public

module ProofSearchOpacitySpine where
  open import LogOS.Packs.Complexity.Experimental.ProofSearchOpacitySpine public
