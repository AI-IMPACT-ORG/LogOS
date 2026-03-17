{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.ConPreorder.Unit where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Terminal/unit boundary.
--
-- Prefer importing this module over re-defining a unit-carrier boundary ad hoc in application
-- packs: local unit-boundary constructions are a common smell in a
-- refinement-first codebase (they erase the observation/refinement structure).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)

UnitPreorder : ∀ {ℓCon ℓRel : Level} → ConPreorder ℓCon ℓRel
UnitPreorder {ℓCon} {ℓRel} =
  record
    { Con   = ⊤ {ℓCon}
    ; _⊑_   = λ _ _ → ⊤ {ℓRel}
    ; refl  = tt
    ; trans = λ _ _ → tt
    }

UnitPreorder₀ : ConPreorder lzero lzero
UnitPreorder₀ = UnitPreorder {ℓCon = lzero} {ℓRel = lzero}
