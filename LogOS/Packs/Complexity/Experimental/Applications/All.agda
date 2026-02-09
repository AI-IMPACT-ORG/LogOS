{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
  import LogOS.Complexity.Model as Model

module PvsNP where
  open import LogOS.Packs.Complexity.Experimental.PvsNP.Public public
  open import LogOS.Complexity.PvsNPLedger public

module ProofSearchOpacitySpine where
  open import LogOS.Packs.Complexity.Experimental.ProofSearchOpacitySpine public
