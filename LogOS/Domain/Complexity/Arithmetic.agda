{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Arithmetic where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc; _+_; _*_) 

-- use stdlib _+_ and _*_

one : ℕ
one = suc zero

pow : ℕ → ℕ → ℕ
pow zero    n = one
pow (suc k) n = n * pow k n
