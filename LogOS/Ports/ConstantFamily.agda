{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.ConstantFamily where

-- Constant-family helpers (uniform semantics as a special case of dependent semantics).
--
-- In v1.1 the canonical “locality is relative” notion is dependent:
--   `LocalityPort X I O` for `O : I → ConPreorder … …`.
--
-- Uniform locality (`O` constant) is a special case, obtained by taking the
-- constant family `λ _ → O`. This module factors out the small boilerplate
-- needed to build the dependent port from uniform probe data.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (View)
open import LogOS.Ports.Locality.Core using (LocalityPort)

constLocalityPort
  : ∀ {ℓX ℓI ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → (I → View X O)
  → LocalityPort X I (λ _ → O)
constLocalityPort probes =
  record { localProbe = probes }
