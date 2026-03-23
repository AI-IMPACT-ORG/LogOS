{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Nat where

-- Peano natural numbers (inductive), not `Agda.Builtin.Nat`.
--
-- Rationale: under Agda 2.8.0, checking `Agda.Builtin.Nat` can emit
-- `CoverageNoExactSplit` on the builtin `_==_` with the repository's
-- `-W all -W error` policy.  We therefore bind our own `ℕ` with
-- `BUILTIN NATURAL` / `NATPLUS` / `NATTIMES` here instead of importing
-- `Agda.Builtin.Nat`, while keeping literals and `zero` / `suc` / `_+_` / `_*_`.

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ _*_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

{-# BUILTIN NATTIMES _*_ #-}
