{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.WellFounded where

open import LogOS.Prelude
-- Local accessibility predicate (kept here so upgrades/transformers can share it
-- without importing a large transitive dependency).
data Acc {ℓ : Level} {A : Set ℓ} (R : A → A → Set ℓ) (x : A) : Set ℓ where
  acc : (∀ y → R y x → Acc R y) → Acc R x
