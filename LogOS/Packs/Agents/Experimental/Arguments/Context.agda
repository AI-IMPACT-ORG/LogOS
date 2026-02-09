{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.Context where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

-- Bundle the common experimental-arguments parameters:
-- a graded kernel plus the ωCPO assumption needed for μ / RG-flow reasoning.
record Context
  {ℓ : Level}
  (Sig : LogOSSignature ℓ)
  (Q : QAdapter ℓ)
  : Set (lsuc (lsuc ℓ))
  where
  field
    K : GradedKernel Sig Q
    ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
             (BulkBoundary.bnd (GradedKernel.BB K))
