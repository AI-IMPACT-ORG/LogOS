{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.Context where

open import LogOS.Prelude
open import LogOS.Apps.ZFC.Stack.ZFCore.Context using (SetContext)
open import LogOS.Apps.ZFC.Models.IterativeSetTree as IST using (V; _∈ᵛ_)

-- The iterative-set tree carrier can be viewed as a `SetContext`, but note:
-- - membership is intensional (defined by child equality in the W-tree),
-- - extensional equality is only the *derived* `_≈_` from that membership,
--   and does not coincide with definitional equality `≡` without quotienting.

ctxᵛ : ∀ {ℓ : Level} → SetContext {lsuc ℓ}
ctxᵛ {ℓ} =
  record
    { SetU = V {ℓ}
    ; _∈_ = _∈ᵛ_
    }

