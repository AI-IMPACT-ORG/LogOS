{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ViewStrictification where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (refl⊑)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder₀)
open import LogOS.LT.View using (View; _⊑[_]_)

import LogOS.API.Strictification as StrictAPI

V : View (⊤ {ℓ = lzero}) UnitPreorder₀
V = record { μ = λ _ → tt }

_ : tt {ℓ = lzero} ⊑[ V ] tt {ℓ = lzero}
_ = refl⊑ UnitPreorder₀ {c = tt}

_ : StrictAPI.View._≃[_]_ (tt {ℓ = lzero}) V (tt {ℓ = lzero})
_ = refl

extensionalUnit : StrictAPI.View.Extensional≃ V (λ _ → ⊤ {ℓ = lzero})
extensionalUnit _ _ _ _ = tt
