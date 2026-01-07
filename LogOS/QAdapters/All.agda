{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.QAdapters.All where

-- Ready-made `QAdapter` instances (quantale + time embedding).

module Nat where
  open import LogOS.QAdapters.QNat public

module Nat2 where
  open import LogOS.QAdapters.QNat2 public

module NatTop where
  open import LogOS.QAdapters.QNatTop public

module NatMul where
  open import LogOS.QAdapters.QNatMul public

-- Convenient top-level names (avoid `scaleOps` clashes).
open import LogOS.QAdapters.QNat public using (QNat) renaming (scaleOps to scaleOpsQNat)
open import LogOS.QAdapters.QNat2 public using (QNat2) renaming (scaleOps to scaleOpsQNat2)
open import LogOS.QAdapters.QNatTop public using (QNatTop) renaming (scaleOps to scaleOpsQNatTop)
open import LogOS.QAdapters.QNatMul public using (QNatMul) renaming (scaleOps to scaleOpsQNatMul)
