{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.ForcingInvariant where

-- ZFC-facing wrapper: forcing/sheaf semantics are invariant under equivalent
-- coverage presentations (refinement-invariant forcing).

open import LogOS.Prelude
open import LogOS.Minimal.Con using (ConPreorder)

open import LogOS.Theorems.Reflection.ForcingSheaves public

module ForcingInvariant {ℓ : Level} {CP : ConPreorder ℓ}
                        (Cov₁ Cov₂ : Coverage CP) where
  open CoverageEq Cov₁ Cov₂ public using (Cover≈; localOp-≈; sheaf-≈)
