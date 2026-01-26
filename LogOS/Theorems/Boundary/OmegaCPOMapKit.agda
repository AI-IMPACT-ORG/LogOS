{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.OmegaCPOMapKit where

-- Small convenience surface for ωCPO maps used by μ-fusion.
--
-- Purpose: downstream code often needs the `OmegaCPOMap` record (a map that is
-- monotone, strict on ⊥, and ω-continuous on chains), plus identity/composition
-- combinators. This module re-exports those pieces under stable names.

open import LogOS.Prelude
open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Truth as Truth

import LogOS.Theorems.Boundary.MuFusion as MuFusion

module For
  {ℓ₁ ℓ₂ : Level}
  (CP₁ : ConPreorder ℓ₁)
  (CP₂ : ConPreorder ℓ₂)
  where
  open MuFusion.For CP₁ CP₂ public using (OmegaCPOMap; mkOmegaCPOMap≡)

idOmegaCPOMap
  : ∀ {ℓ : Level}
    (CP : ConPreorder ℓ)
    {ω : Truth.GuardedCore.OmegaCPO CP}
  → let module MF = MuFusion.For CP CP in MF.OmegaCPOMap ω ω (λ x → x)
idOmegaCPOMap CP {ω} = MuFusion.Endo.idOmegaCPOMap CP {ω = ω}

composeOmegaCPOMap = MuFusion.Compose.composeOmegaCPOMap
