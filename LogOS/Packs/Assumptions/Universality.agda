{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Assumptions.Universality where

-- Computer science bundle: kernel-as-process presentation for schemes/tasks.
-- This is intentionally conservative: it adds no new axioms, only packages a
-- chosen step-grade to expose `CodeProcess`/`BoundaryProcess`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.API.Assumptions.Core
import LogOS.Computation.KernelUniversalProcess as KUP

record UniversalityBundle {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    stepGrade : QAdapter.Scale (LogicCore.Q C)

  module Process = KUP.ForLogicKernel (LogicCore.K C) stepGrade
  open Process public using (BoundaryProcess; CodeProcess; decodeHom; decodeHomLax)

open UniversalityBundle public
