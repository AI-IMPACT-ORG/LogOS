{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractCausalLandauer2Cat where

-- Minimal thermodynamic layer over the causal physical category.
--
-- This is the default irreversibility-facing cost stack:
-- locality is retained through the physical base, causality is explicit,
-- and Landauer bounds can decorate arbitrary causal kernel morphisms over the
-- chosen shared boundary, not only the reversible/pointwise Deutsch slice.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
open import LogOS.Ports.Valuation.QAdapter using (QAdapter)

import LogOS.Ports.AbstractCausal2Cat as Causal2Cat
import LogOS.Ports.AbstractLandauerStack2Cat as LandauerStack2Cat

module CausalLandauer2CatLocal
  {ℓI ℓOCon ℓORel ℓCode ℓQ : Level}
  (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  (Q : QAdapter ℓQ)
  where

  C : Thin2Cat _ _ _
  C = Causal2Cat.Causal2CatLocal.WithPort {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS

  module Landauer =
    LandauerStack2Cat.LandauerStack2CatLocal C Q

  Scale = Landauer.Scale
  JP = Landauer.JP

  open Landauer public using
    ( landauer
    ; landauerPort
    ; stack2Cat
    ; Displayed
    ; WithPort
    ; forget
    ; baseObj
    ; baseHom
    )
    renaming
      ( LandauerStackAssumptions to CausalLandauerAssumptions
      ; LandauerStack to CausalLandauerStack
      )

open CausalLandauer2CatLocal public using
  ( C
  ; Scale
  ; JP
  ; CausalLandauerAssumptions
  ; landauer
  ; CausalLandauerStack
  ; landauerPort
  ; stack2Cat
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )
