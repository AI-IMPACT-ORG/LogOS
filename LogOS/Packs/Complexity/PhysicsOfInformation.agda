{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Complexity.PhysicsOfInformation where

-- Curated, paper-facing “physics of information” surface.
--
-- Goal: stable names for the Second-Law/Landauer storyline, without requiring
-- readers to chase deep module paths.

open import LogOS.Domain.Complexity.SecondLaw public
  using (SecondLawAssumptions; merge→entropy+; landauerFromLCU)

open import LogOS.Theorems.Meta.Landauer public
  using (LandauerAssumptions; landauer)

open import LogOS.Theorems.Meta.LandauerIO public
  using (LandauerIOAssumptions; landauer-io; comp-bound; tensor-bound)

-- Paper-friendly alias names (kept stable via Tests/CoherenceSurfaces.agda).

merge-implies-entropy-increase = merge→entropy+

landauer-pack-from-lcu = landauerFromLCU

irreversible-io-cost-lower-bound = landauer-io
