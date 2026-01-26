{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.End where

open import LogOS.Prelude
open import LogOS.Algebra.Ring

-- Endomorphisms over a finite carrier V, abstracted as a matrix-like structure.

record End {ℓ : Level} (R : Ring {ℓ}) (V : Set ℓ) : Set (lsuc ℓ) where
  open Ring R
  infixl 6 _+M_
  field
    Mat    : Set ℓ
    I      : Mat
    _+M_   : Mat → Mat → Mat
    scaleM : Ring.Carrier R → Mat → Mat
    det    : Mat → Ring.Carrier R

open End public
