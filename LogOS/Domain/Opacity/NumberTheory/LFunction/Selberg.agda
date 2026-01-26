{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.Selberg where

open import LogOS.Prelude

open import LogOS.Algebra.Ring
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Core as LC

-- Selberg-style pack: completed FE is immediate from Z-FE + Gamma symmetry

record SelbergPack {ℓ : Level} (R : Ring {ℓ}) : Set (lsuc ℓ) where
  field
    LF   : LC.LFunction R
    ZFE  : LC.LZ-FE LF
    GS   : LC.GammaSym LF

  lambdaFE : ∀ {u} → LC.LFunction.In LF u → LC.LFunction.Lambda LF u ≡ LC.LFunction.Lambda LF (LC.LFunction.mirror LF u)
  lambdaFE = LC.LambdaFE-from-LZ+Gamma LF ZFE GS
