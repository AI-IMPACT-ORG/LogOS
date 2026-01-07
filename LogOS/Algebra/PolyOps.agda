{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.PolyOps where

open import LogOS.Prelude
open import Data.Nat using (ℕ)
open import LogOS.Algebra.Ring

record PolyOps {ℓ : Level} (R : Ring {ℓ}) : Set (lsuc ℓ) where
  open Ring R
  field
    pow    : Ring.Carrier R → ℕ → Ring.Carrier R
    scaleR : Ring.Carrier R → Ring.Carrier R → Ring.Carrier R

open PolyOps public
