{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.All where

-- Computational universality pack:
-- - universal IR
-- - compilation of multiple “computation presentations” into the same IR
--   (Turing/Minsky, quantum circuits, Ethereum-like stack machine, …)

open import LogOS.API.Minimal public

module UniversalIR where
  open import LogOS.Models.UniversalIR.Core public

module Universality where
  open import LogOS.Models.Universality.Core public

module Complexity where
  open import LogOS.Domain.Complexity.UniversalIRCM public
