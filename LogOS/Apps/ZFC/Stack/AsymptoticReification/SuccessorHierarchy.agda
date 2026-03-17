{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorHierarchy where

-- Canonical stage-by-stage hierarchy packaging for ZFC-style late collapse.
--
-- This module packages only the canonical rung family and the canonical
-- successor bridge between adjacent stages. Same-stage completion remains a
-- separate optional layer.

open import LogOS.Prelude
open import LogOS.LT.Stage.SuccessorChain using (SuccessorChain)

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as Canonical
import LogOS.Apps.ZFC.Stack.AsymptoticReification.SuccessorBridge as Bridge
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

record SuccessorHierarchy {ℓStage : Level} {Stage : Set ℓStage} (Chain : SuccessorChain Stage) : Setω where
  open SuccessorChain Chain using (next)

  field
    ctxLevel : Stage -> Level
    ctxAt : (i : Stage) -> ZF.SetContext {ctxLevel i}
    rungAt : (i : Stage) -> Canonical.CanonicalRung (ctxAt i)

  SuccessorBridgeAt : (i : Stage) -> Set (lsuc (lsuc (ctxLevel (next i) ⊔ ctxLevel i)))
  SuccessorBridgeAt i =
    let
      K = rungAt i
      module R = Canonical.CanonicalRung K
    in
    Bridge.SuccessorBridge R.base (ctxAt (next i))

  field
    successorBridge : (i : Stage) -> SuccessorBridgeAt i

open SuccessorHierarchy public
