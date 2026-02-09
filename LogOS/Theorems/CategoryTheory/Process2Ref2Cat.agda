{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Process2Ref2Cat where

-- CategoryTheory-facing wrapper: expose the process Thin2Cat as a refinement
-- 2-category (`Ref2CatCore`) so downstream developments can use one uniform
-- interface for:
-- - objects: processes,
-- - 1-cells: lax process morphisms,
-- - 2-cells: pointwise refinement on the map.

open import LogOS.Prelude

import LogOS.Computation.Process2Cat as Proc2
import LogOS.Theorems.CategoryTheory.WrapperCore as Wrap

module For
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  where

  module C = Proc2.For {ℓO = ℓO} {ℓC = ℓC} {ℓQ = ℓQ} {Output = Output}

  ProcessRef2CatCore
    : Wrap.Ref2CatCore
        (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
        (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
        ℓC
  ProcessRef2CatCore = Wrap.RelThin2Cat→Ref2CatCore C.ProcessRelThin2Cat
