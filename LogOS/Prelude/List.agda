{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.List where

open import LogOS.Host.Level using (Level)

infixr 5 _∷_

-- Minimal, universe-polymorphic list type.
data List {ℓ : Level} (A : Set ℓ) : Set ℓ where
  []  : List A
  _∷_ : A → List A → List A

