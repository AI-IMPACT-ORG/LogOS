{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.Reachability where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded

import LogOS.Minimal.Reachability.Graded as R
import LogOS.Minimal.Truth as Truth

-- Boundary reachability induced by the kernel’s graded guarded truth closure.
--
-- This is the canonical “budgeted reachability” relation for graded kernels:
-- it talks only about boundary constraints and the closure `GTruth`.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where

  open GradedKernel K

  CP∂ : ConPoset ℓ
  CP∂ = BulkBoundary.bnd BB

  module CP∂ = ConPoset CP∂

  module Reach = R.For {Q = Q} {CP = CP∂} GTruth

  infix 4 _⟶[_]_ _⟶⋆_

  _⟶[_]_ : CP∂.Con → QAdapter.Scale Q → CP∂.Con → Set ℓ
  _⟶[_]_ = Reach._⟶[_]_

  -- “Saturation reachability”: reachability at the closure’s designated saturation grade.
  _⟶⋆_ : CP∂.Con → CP∂.Con → Set ℓ
  c ⟶⋆ d = c ⟶[ Truth.GuardedCore.GradedClosure.sat GTruth ] d

  ⟶⋆-refl : ∀ c → c ⟶⋆ c
  ⟶⋆-refl c = Reach.satReach-refl c

  -- Re-export the generic reachability laws specialised to this kernel.
  open Reach public using
    ( ⟶-mono-grade
    ; ⟶-mono-src
    ; ⟶-mono-tgt
    ; ⟶-comp
    ; ⟶-⊔g₁
    ; ⟶-⊔g₂
    ; ⟶-⊔g
    )
