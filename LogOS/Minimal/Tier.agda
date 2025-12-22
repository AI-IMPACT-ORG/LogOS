{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Tier where

-- Minimal tier index for Strict / Homotypical / Guarded

data Tier : Set where
  S H G : Tier
