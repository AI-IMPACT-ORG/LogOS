{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.All where

-- Ready-made `QAdapter` instances (quantale + time homomorphism `τ`).

module Nat where
  open import LogOS.QAdapters.QNat public

module Nat2 where
  open import LogOS.QAdapters.QNat2 public

module NatTop where
  open import LogOS.QAdapters.QNatTop public

module NatMul where
  open import LogOS.QAdapters.QNatMul public

module Guards where
  open import LogOS.QAdapters.Guards public

-- Convenient top-level names (avoid `scaleOps` clashes).
--
-- Note: `QNatTop` has a top grade `ω` (no ℕ readout can be order-sound), so its
-- operational `ScaleOps` lives under `LogOS.QAdapters.QNatTop.scaleOpsTrunc`
-- and is intentionally *not* re-exported here.
open import LogOS.QAdapters.QNat public
  using (QNat)
  renaming
    ( scaleOps     to scaleOpsQNat
    ; scaleOpsLaws to scaleOpsLawsQNat
    ; budgetOps    to budgetOpsQNat
    )
open import LogOS.QAdapters.QNat2 public
  using (QNat2)
  renaming
    ( scaleOps     to scaleOpsQNat2
    ; scaleOpsLaws to scaleOpsLawsQNat2
    ; budgetOps    to budgetOpsQNat2
    )
open import LogOS.QAdapters.QNatTop public using (QNatTop)
open import LogOS.QAdapters.QNatMul public
  using (QNatMul)
  renaming
    ( scaleOps     to scaleOpsQNatMul
    ; scaleOpsLaws to scaleOpsLawsQNatMul
    ; budgetOps    to budgetOpsQNatMul
    )
