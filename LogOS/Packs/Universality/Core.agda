{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Universality.Core where

-- Curated, stable universality surface (no demos).

open import LogOS.Prelude
open import LogOS.Domain.Universality.Core public

-- Stable scheme presentation of the universality core.
module CoreScheme where
  import LogOS.Domain.Universality.SchemePresentation as SP
  import LogOS.Computation.Scheme as Scheme

  runCore : ∀ n u → CoreUCode
  runCore n u = Scheme.run SP.CoreScheme (SP.mkInput n u)

  runCore-simulate : ∀ n u → runCore n u ≡ simulateCoreU n u
  runCore-simulate n u = SP.run-simulate n u
