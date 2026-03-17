{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.PhysicalOptional.PreQuantum where

-- Curated optional API for purification over the causal + Landauer spine.
--
-- This surface exports the actual stacked categorical interface and
-- uniqueness-first accessors for the two public ports, rather than the raw
-- duplicate-tag stack lane.

open import LogOS.Ports.PreQuantum.AbstractCausalPreQuantum2Cat public using
  ( CausalPreQuantumAssumptions
  ; C
  ; Scale
  ; JP
  ; CausalPreQuantumUniqueStack
  ; landauerUniquePort
  ; purificationUniquePort
  ; stack2Cat
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )

open import LogOS.Ports.AbstractLandauer2Cat public using (LandauerTag)
open import LogOS.Ports.PreQuantum.Purification2Cat public using (PurificationTag)
