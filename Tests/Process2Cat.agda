{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.Process2Cat where

-- Smoke test: processes and lax process morphisms form a Thin2Cat, with 2-cells
-- as pointwise refinement of the state translation map.

open import LogOS.Prelude
open import LogOS.Minimal.Thin2Cat using (Thin2CatLaws)

import LogOS.Computation.Process2Cat as Proc2
import LogOS.Theorems.CategoryTheory.Process2Ref2Cat as Proc2CT

module _ {ℓO ℓC ℓQ : Level} {Output : Set ℓO} where
  module C = Proc2.For {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} {Output = Output}
  module W = Proc2CT.For {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} {Output = Output}

  laws : Thin2CatLaws C.ProcessThin2Cat
  laws = C.ProcessThin2CatLaws

  -- Also available as a refinement 2-category core.
  core : _
  core = W.ProcessRef2CatCore
