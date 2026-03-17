{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.PhysicalOptional.Deutsch where

-- Curated optional API for the reversible Deutsch slice over the causal base.

open import LogOS.Prelude using (Level)
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat as AbstractDeutsch2Cat

module DeutschSlice
  {ℓI ℓOCon ℓORel ℓCode : Level}
  (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  where

  module Raw = AbstractDeutsch2Cat.Deutsch2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS

  module Locality = Raw.Locality
  module Causality = Raw.Causality
  module Reversibility = Raw.Reversibility
  module Deutsch = Raw.Deutsch

open import LogOS.Ports.AbstractDeutschNoCloning public using
  ( Indiscrete
  ; diag-section→indiscrete
  ; stableClone
  ; stableClone-law
  )
