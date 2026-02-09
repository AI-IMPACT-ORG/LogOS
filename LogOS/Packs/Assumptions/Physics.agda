{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Assumptions.Physics where

-- Physics / physics-of-information bundle:
-- - Landauer / Second-Law assumptions over the shared signature+adapter.
-- - PvNP is exposed via the separate `PvsNPLedger` interface (orthogonal to
--   Landauer/Second-Law); we re-export the ledger module for convenience.

open import LogOS.Prelude

open import LogOS.API.Assumptions.Core

open import LogOS.Complexity.PvsNPLedger public

open import LogOS.Complexity.SecondLaw using (SecondLawAssumptions; SecondLawGuards)
open import LogOS.Theorems.Meta.Landauer using (LandauerAssumptions)

record PhysicsOfInformationBundle {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    landauer : LandauerAssumptions (LogicCore.Sig C) (LogicCore.Q C)
    secondLaw : SecondLawAssumptions (LogicCore.Sig C) (LogicCore.Q C)
    secondLawGuards : SecondLawGuards (LogicCore.Sig C) (LogicCore.Q C) secondLaw

open PhysicsOfInformationBundle public
