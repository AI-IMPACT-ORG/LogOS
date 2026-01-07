{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Examples.NeuralSymbolicBlend where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Learning.SoftPolicy as Soft

-- A minimal neural-symbolic blend:
-- soft (graded) updates refined by a hard symbolic constraint.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  where

  open GradedKernel K using (BB)
  open BulkBoundary BB using (Con_bnd)

  module L = Soft.For K
  open L using (Policy; SoftUpdate; applySoft; blend)

  Symbolic : Set ℓ
  Symbolic = Con_bnd

  refine : Policy → Symbolic → Policy
  refine p sym = blend p sym

  stepRefine : ∀ {g} → SoftUpdate g → Symbolic → Policy → Policy
  stepRefine step sym p = refine (applySoft step p) sym
