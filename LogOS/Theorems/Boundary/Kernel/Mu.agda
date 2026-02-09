{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Kernel.Mu where

-- Boundary-facing μ / Kleene fixed-point utilities instantiated at a `Kernel`.
--
-- Motivation: many application packs (notably Agents) work with `Kernel`
-- directly; this module provides the same “turnkey” Kleene μ-calculus surface
-- as `LogOS.Theorems.Boundary.Mu.Kleene`, but without requiring access to a full
-- `Kernel` value.

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel using (Kernel; module Kernel)

-- ============================================================================
-- Generic Kleene μ on a boundary ωCPO (independent of `Th*`)
-- ============================================================================

module Kleene
  {ℓ}
  (Sig : LogOSSignature ℓ)
  (Q   : QAdapter ℓ)
  (K   : Kernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (Kernel.BB K)))
  where

  private
    module GT = Truth.GuardedCore
    CP = BulkBoundary.bnd (Kernel.BB K)

  open ConPreorder CP public
  open GT.OmegaCPO ωCPO public

  module μ = GT.Kleene ωCPO

  -- Re-export the core definitions and theorems specialised to the logic-kernel boundary.
  iter = μ.iter
  μF   = μ.μ

  μF-unfold-left = μ.μ-unfold-left
  μF-induction   = μ.μ-induction

  ScottContinuous = μ.ScottContinuous
  μF-unfold-right = μ.μ-unfold-right

  iter-mono-chain-infl = μ.iter-mono-chain-infl
  μF-unfold-right-infl = μ.μ-unfold-right-infl
