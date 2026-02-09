{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Presentation2Ref2Cat where

-- CategoryTheory-facing wrapper: expose the presentation Thin2Cat as a
-- refinement 2-category (`Ref2CatCore`).
--
-- This stays kernel-independent: it is formulated purely over a fixed
-- satisfaction system and semantic translations between presentations.

open import LogOS.Prelude

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem)
import LogOS.Ports.Semantic.Presentation2Cat as P2
import LogOS.Theorems.CategoryTheory.WrapperCore as Wrap

module For
  {ℓCtx ℓCon ℓSat ℓForm : Level}
  (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
  where

  module C = P2.For {ℓForm = ℓForm} {S = S}

  PresentationRef2CatCore
    : Wrap.Ref2CatCore
        (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm))
        (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm))
        (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  PresentationRef2CatCore = Wrap.RelThin2Cat→Ref2CatCore C.PresentationRelThin2Cat
