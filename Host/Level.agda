{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Host.Level where

-- Host wrapper around Agda.Primitive to provide Level, lzero, lsuc, _⊔_,
-- and a minimal Lift/lift compatible with usages in this project.

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_)

-- Minimal Lift type (std-lib style): lift A into a higher universe.
record Lift {a : Level} (ℓ : Level) (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
-- Note: this `Lift` is intentionally not tied to Agda builtins, to keep the
-- development conservative across compiler versions.
