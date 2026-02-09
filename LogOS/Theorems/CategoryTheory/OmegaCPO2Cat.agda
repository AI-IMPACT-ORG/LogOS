{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.OmegaCPO2Cat where

-- CategoryTheory-facing wrapper: expose the ωCPO-map Thin2Cat as a refinement
-- 2-category (`Ref2CatCore`).
--
-- This is the “domain-theory bookkeeping spine” that μ-fusion and limit/stability
-- theorems rely on.

open import LogOS.Prelude

import LogOS.Theorems.Boundary.OmegaCPOMap2Cat as Ω2
import LogOS.Theorems.CategoryTheory.WrapperCore as Wrap

module For {ℓ : Level} where
  module C = Ω2.For {ℓ = ℓ}

  OmegaCPORef2CatCore : Wrap.Ref2CatCore (lsuc ℓ) (lsuc ℓ) ℓ
  OmegaCPORef2CatCore = Wrap.RelThin2Cat→Ref2CatCore C.OmegaCPORelThin2Cat
