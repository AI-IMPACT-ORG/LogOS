{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Learning.RGFlow where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow.Core as RGCore

-- Wrapper: re-export `Core` and keep the physics overlay discoverable, without
-- forcing downstream users to import the physics assumptions.
--
-- Note: we do *not* import `RGFlow.Physics` or `RGFlow.Info` here, because
-- importing them would force typechecking the full physics-of-information /
-- complexity stack (slow, and not needed for most uses). Import
-- `LogOS.Packs.Agents.Experimental.Learning.RGFlow.Physics` or
-- `LogOS.Packs.Agents.Experimental.Learning.RGFlow.Info` explicitly when you
-- want the additional assumptions/lemmas.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module CoreFor = RGCore.For K ωCPO
  open CoreFor public

module Core where
  open import LogOS.Packs.Agents.Experimental.Learning.RGFlow.Core public
