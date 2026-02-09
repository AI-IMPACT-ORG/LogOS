{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.DataProcessingInequality where

open import LogOS.Prelude

open import LogOS.Prelude using (ℕ)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; trans≤ℕ) public
open import LogOS.Minimal.Con using (ConPreorder)

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

-- --------------------------------------------------------------------------
-- More general (and less vacuous) DPI interface: explicit channel family + value preorder.
-- --------------------------------------------------------------------------

record ChannelFamily {ℓObs ℓCh : Level} (Obs : Set ℓObs) : Set (lsuc (ℓObs ⊔ ℓCh)) where
  field
    Ch  : Set ℓCh
    run : Ch → Obs → Obs

record DPIOn
  {ℓObs ℓCh ℓI : Level}
  (Obs : Set ℓObs)
  (CF  : ChannelFamily {ℓObs = ℓObs} {ℓCh = ℓCh} Obs)
  (IP  : ConPreorder ℓI)
  : Set (lsuc (ℓObs ⊔ ℓCh ⊔ ℓI)) where

  open ChannelFamily CF
  open ConPreorder IP

  field
    info : Obs → Con
    dpi  : ∀ (C : Ch) (o : Obs) → _⊑_ (info (run C o)) (info o)

module DerivedOn
  {ℓObs ℓCh ℓI : Level}
  {Obs : Set ℓObs}
  {CF  : ChannelFamily {ℓObs = ℓObs} {ℓCh = ℓCh} Obs}
  {IP  : ConPreorder ℓI}
  (D : DPIOn Obs CF IP)
  where

  open DPIOn D
  open ChannelFamily CF
  open ConPreorder IP

  dpi²
    : ∀ (C₁ C₂ : Ch) (o : Obs)
      → _⊑_ (info (run C₂ (run C₁ o))) (info o)
  dpi² C₁ C₂ o = ConPreorder.trans IP (dpi C₂ (run C₁ o)) (dpi C₁ o)
