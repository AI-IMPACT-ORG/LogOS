{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.QNatTop where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; _+_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps)

-- Nat-valued grades with a trivial order (every grade ≤ every grade).
-- This gives concrete step-count grades while satisfying sat-top.

QNatTop : QAdapter lzero
QNatTop = record
  { Scale = ℕ
  ; _≤s_  = λ _ _ → ⊤
  ; _·_   = _+_
  ; e     = zero
  ; _≤p_  = λ _ _ → ⊤
  ; Time  = ℕ
  ; _+_   = _+_
  ; zero  = zero
  ; τ     = λ n → n
  }

scaleOps : ScaleOps QNatTop
scaleOps = record { budget = λ n → n ; steps = λ n → n }
