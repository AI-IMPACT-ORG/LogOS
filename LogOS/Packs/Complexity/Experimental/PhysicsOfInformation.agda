{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.Experimental.PhysicsOfInformation where

-- Curated, paper-facing “physics of information” surface (experimental).
--
-- Goal: stable names for the Second-Law/Landauer storyline, without requiring
-- readers to chase deep module paths.

open import LogOS.Packs.Trust using (PackTrust)
import LogOS.Packs.Complexity.Experimental.Core as PackCore

packTrust : PackTrust
packTrust = PackCore.packTrust

open import LogOS.Complexity.SecondLaw public
  using (SecondLawAssumptions; SecondLawGuards; merge→entropy+; nonvacuous-entropy+; landauerFromLCU)

open import LogOS.Theorems.Meta.Landauer public
  using (LandauerAssumptions; landauer)

open import LogOS.Theorems.Meta.LandauerIO public
  using (LandauerIOAssumptions; landauer-io; comp-bound; tensor-bound; CostMono; landauer-io-refine)

-- Paper-friendly alias names (kept stable via Tests/CoherenceSurfaces.agda).

merge-implies-entropy-increase = merge→entropy+

landauer-pack-from-lcu = landauerFromLCU

irreversible-io-cost-lower-bound = landauer-io
