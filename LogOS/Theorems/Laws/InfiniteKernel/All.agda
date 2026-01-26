{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Laws.InfiniteKernel.All where

-- Infinite kernel laws (limit/ω-chain structure available).

open import LogOS.Kernel.Infinite.Lemmas public
open import LogOS.Theorems.Capstone.Approximation public
open import LogOS.Theorems.Capstone.ClosureCalculus public
open import LogOS.Theorems.Capstone.StabilityTruth public

module Graded where
  open import LogOS.Theorems.Laws.InfiniteKernel.Graded.All public
