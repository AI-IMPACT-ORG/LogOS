{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.DataProcessingInequality where

open import LogOS.Prelude

open import Data.Nat using (ℕ)
open import Data.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ) public

-- A minimal, LogOS-native Data Processing Inequality (DPI) layer.
--
-- We intentionally avoid measure theory / probability: this is a *resource interface*
-- for “classical information” carried by observables, and a class of admissible
-- post-processings (channels). The only law we need is monotonicity:
-- processing cannot increase information.
--
-- This is designed to plug into complexity/resource arguments:
-- if correctness requires extracting `need n` bits of classical information,
-- DPI + capacity/throughput bounds can show infeasibility for poly budgets.

-- A family of admissible processings (channels) over observables `Obs`.
record Channel {ℓ : Level} (Obs : Set ℓ) : Set (lsuc ℓ) where
  field
    run : Obs → Obs

-- DPI assumption pack: `info` is monotone decreasing under any channel.
record DPI {ℓ : Level} (Obs : Set ℓ) : Set (lsuc ℓ) where
  field
    info : Obs → ℕ
    dpi  : ∀ (C : Channel Obs) (o : Obs) → info (Channel.run C o) ≤ℕ info o

-- Derived closure: multiple processing steps never increase information.
module Derived {ℓ : Level} {Obs : Set ℓ} (D : DPI Obs) where
  open DPI D

  dpi²
    : ∀ (C₁ C₂ : Channel Obs) (o : Obs)
      → info (Channel.run C₂ (Channel.run C₁ o)) ≤ℕ info o
  dpi² C₁ C₂ o = trans≤ℕ (dpi C₂ (Channel.run C₁ o)) (dpi C₁ o)
