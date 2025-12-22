{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.QNat where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; _+_)
open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.ScaleOps using (ScaleOps)

-- Numeric quantale+time adapter: costs are naturals with preorder ≤ and monoid +.
-- This is the default “step counting / time” adapter used by many demos.

QNat : QAdapter lzero
QNat = record
  { Scale = ℕ
  ; _≤s_  = _≤ℕ_
  ; _·_   = _+_
  ; e     = zero
  ; _≤p_  = _≤ℕ_
  ; Time  = ℕ
  ; _+_   = _+_
  ; zero  = zero
  ; τ     = λ n → n
  }

scaleOps : ScaleOps QNat
scaleOps = record { budget = λ n → n ; steps = λ n → n }
