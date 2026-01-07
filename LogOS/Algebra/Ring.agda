{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Algebra.Ring where

open import LogOS.Prelude hiding (_+_; _*_)

-- Minimal ring interface used by determinant/ζ patterns and examples.

record Ring {ℓ : Level} : Set (lsuc ℓ) where
  infixl 6 _+_
  infixl 7 _*_
  infix  8 -_
  field
    Carrier : Set ℓ
    0# 1#   : Carrier
    _+_ _*_ : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    inv     : Carrier → Carrier

open Ring public
