{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.SpectralPack where

open import LogOS.Prelude

-- A minimal spectral-interface record: a type of spectral points together with
-- a critical-line predicate and a nontrivial-zero predicate.
--
-- This is intentionally generic and operator-free; it is used as the common
-- interface for GRH/RH adapters and projector/nucleus bridges.

record SpectralPack (ℓS : Level) : Set (lsuc ℓS) where
  field
    Spectral       : Set ℓS
    OnLine         : Spectral → Set ℓS
    NontrivialZero : Spectral → Set ℓS

open SpectralPack public
