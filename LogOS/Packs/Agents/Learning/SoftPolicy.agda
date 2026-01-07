{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Learning.SoftPolicy where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Algebra.ConAlg using (ConAlg)

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.Graded.Endo as GEndo
open import LogOS.Kernel.Graded.ConAlgOf using (conAlgOf)

-- Soft policies are graded: updates carry a strength/temperature in the kernel's scale.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where

  open GradedKernel K using (BB)
  open BulkBoundary BB using (Con_bnd)
  open GEndo

  Policy : Set ℓ
  Policy = Con_bnd

  SoftUpdate : QAdapter.Scale Q → Set (lsuc ℓ)
  SoftUpdate g = ClosureStepAt K g

  applySoft : ∀ {g} → SoftUpdate g → Policy → Policy
  applySoft s = Endo.fn (ClosureStepAt.endo s)

  -- Forget the grade: soft update becomes a hard (saturation-grade) step.
  harden : ∀ {g} → SoftUpdate g → ClosureStep K
  harden = toSatStep

  -- Compose soft updates; grades multiply.
  infixl 9 _thenSoft_
  _thenSoft_ : ∀ {g₁ g₂}
    → SoftUpdate g₁ → SoftUpdate g₂ → SoftUpdate (QAdapter._·_ Q g₁ g₂)
  _thenSoft_ = _thenStepAt_

  promoteSoft : ∀ {g g'} → QAdapter._≤s_ Q g g' → SoftUpdate g → SoftUpdate g'
  promoteSoft = promoteStep

  conAlg : ConAlg {ℓ}
  conAlg = conAlgOf K

  open ConAlg conAlg using (_⊗∂_; I∂)

  blend : Policy → Policy → Policy
  blend = _⊗∂_

  identity : Policy
  identity = I∂
