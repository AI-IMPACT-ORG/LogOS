{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Nat where

-- Host-minimal natural numbers.
--
-- We intentionally avoid importing `Agda.Builtin.Nat` here. Recent Agda toolchains
-- can emit `CoverageNoExactSplit` warnings inside that builtin module, and LogOS
-- treats warnings as errors in CI. Keeping `ℕ` defined locally preserves the
-- refinement-first posture and removes that upstream warning source.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * _ = zero
suc m * n = n + (m * n)

