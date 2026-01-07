{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.All where

-- Boundary-facing theorems: fixed points, continuity, μ-induction wrappers,
-- and boundary observation/reflection utilities.

open import LogOS.Theorems.Boundary.Reflection public
open import LogOS.Theorems.Boundary.Mu public
open import LogOS.Theorems.Boundary.Continuity public
open import LogOS.Theorems.Boundary.Guarded public
open import LogOS.Theorems.Boundary.Communication public
open import LogOS.Ports.Semantic.InterlinguaCore public
  using (PresentationC; canonicalPresentation; presentation-to-canonical; translate-id-core; translate-comp-core)
open import LogOS.Ports.Semantic.Interlingua public
open import LogOS.Theorems.Boundary.SpectralSeparation public
open import LogOS.Theorems.Boundary.QuickWins public
