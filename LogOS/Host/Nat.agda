{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Nat where

-- Host wrapper around Agda.Builtin.Nat.
--
-- Keep the LogOS nat seam narrow: we expose only the primitive Peano surface
-- used throughout the repository, not the builtin Boolean comparison helpers.
-- This preserves the customary `ℕ` name without turning builtin `_==_`/`_<_`
-- into part of the public LogOS host API.

import Agda.Builtin.Nat as BuiltinNat

ℕ : Set
ℕ = BuiltinNat.Nat

pattern zero = BuiltinNat.zero
pattern suc n = BuiltinNat.suc n

infixl 6 _+_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
_+_ = BuiltinNat._+_

_*_ : ℕ → ℕ → ℕ
_*_ = BuiltinNat._*_
