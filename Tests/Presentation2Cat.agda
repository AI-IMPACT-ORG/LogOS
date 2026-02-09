{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.Presentation2Cat where

-- Smoke test: presentations of a fixed satisfaction system form a Thin2Cat
-- under semantic translations, with 2-cells as refinement of translated meaning.

open import LogOS.Prelude

open import LogOS.Ports.Semantic.PresentationCore using (SatSystem; satSystem)
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.HeteroInterlinguaCore using (canonicalPresentation)
open import LogOS.Minimal.Thin2Cat using (Thin2CatLaws)

import LogOS.Ports.Semantic.Presentation2Cat as P2
import LogOS.Theorems.CategoryTheory.Presentation2Ref2Cat as P2CT

S : SatSystem {ℓCtx = lzero} {ℓCon = lzero} {ℓSat = lzero}
S = satSystem (⊤ {ℓ = lzero}) (⊤ {ℓ = lzero}) (λ _ _ → ⊤ {ℓ = lzero})

P : PresentationC {ℓForm = lzero} S
P = canonicalPresentation S

module C = P2.For {ℓForm = lzero} {S = S}
module W = P2CT.For {ℓCtx = lzero} {ℓCon = lzero} {ℓSat = lzero} {ℓForm = lzero} S

laws : Thin2CatLaws C.PresentationThin2Cat
laws = C.PresentationThin2CatLaws

-- Also available as a refinement 2-category core.
core : _
core = W.PresentationRef2CatCore
