{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Level where

-- Thin wrapper around Agda.Primitive to provide Level, lzero, lsuc, _⊔_,
-- and a minimal Lift/lift compatible with usages in this project.

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_)

-- Minimal Lift type (std-lib style): lift A into a higher universe.
record Lift {a : Level} (ℓ : Level) (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A
