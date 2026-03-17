{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.PhysicalOptional.Causal where

-- Curated optional API for the ambient causal physical base.

open import LogOS.Ports.AbstractCausal2Cat public using
  ( PhysicalKernel
  ; kernel
  ; LOGᵏ
  ; CausalTag
  ; CausalOb
  ; port2Cat
  ; singleton
  ; stack
  ; port
  ; Displayed
  ; WithPort
  ; forget
  ; causalObj
  ; CausalDisplayedHom
  ; mkCausalHom
  ; causalKernelOf
  ; causalToKernelHom
  ; causalFlowWitness
  )
