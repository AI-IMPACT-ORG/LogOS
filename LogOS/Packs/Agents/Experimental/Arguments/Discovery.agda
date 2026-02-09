{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.Discovery where

-- Single entrypoint for discovery-driven developments (experimental).
-- Kept lightweight so docs/papers can reference one stable path.

module Scaling where
  open import LogOS.Packs.Agents.Experimental.Arguments.DiscoveryScaling public

module Kolmogorov where
  import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovDiscoveryScaling as KDS
  import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality as KO

  module DiscoveryScaling = KDS
  module Optimality = KO

module Solomonoff where
  open import LogOS.Packs.Agents.Experimental.Arguments.SolomonoffLearning public
