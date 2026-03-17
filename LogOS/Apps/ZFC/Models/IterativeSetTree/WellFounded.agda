{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.WellFounded where

open import LogOS.Prelude

import LogOS.Apps.ZFC.Models.IterativeSetTree as IST
import LogOS.Apps.ZFC.Models.IterativeSetTree.Context as Ctx
import LogOS.Apps.ZFC.Stack.WellFounded as WF
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

wfᵛ : ∀ {ℓ : Level} → (x : IST.V {ℓ}) → WF.Acc IST._∈ᵛ_ x
wfᵛ (IST.sup I f) =
  WF.acc step
  where
    step : ∀ y → IST._∈ᵛ_ y (IST.sup I f) → WF.Acc IST._∈ᵛ_ y
    step y (i , eq) = subst (WF.Acc IST._∈ᵛ_) (sym eq) (wfᵛ (f i))

wfCtxᵛ
  : ∀ {ℓ : Level}
  → (x : ZF.SetContext.SetU (Ctx.ctxᵛ {ℓ}))
  → WF.Acc (ZF.SetContext._∈_ (Ctx.ctxᵛ {ℓ})) x
wfCtxᵛ = wfᵛ
