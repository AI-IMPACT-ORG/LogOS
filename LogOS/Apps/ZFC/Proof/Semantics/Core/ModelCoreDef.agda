{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Core.ModelCoreDef where

open import LogOS.Prelude using (Level)

open import LogOS.Apps.ZFC.Proof.Semantics.Core.ModelDef using (Model)

import LogOS.Apps.ZFC.Proof.Semantics.Core.PrimOps as PrimOps
import LogOS.Apps.ZFC.Proof.Semantics.Core.Congruence as Cong
import LogOS.Apps.ZFC.Proof.Semantics.Core.RenameSemantics as RenSem
import LogOS.Apps.ZFC.Proof.Semantics.Core.LiftSubst as LiftSubst

module ModelCore {ℓ : Level} (M : Model {ℓ}) where
  open PrimOps.ForModel M public
  open Cong.ForModel M public
  open RenSem.ForModel M public using
    ( evalTerm-rename
    ; evalFormula-rename
    )
  open LiftSubst.ForModel M public using
    ( tailVal
    ; insertAt
    ; insertAt-suc-extend
    ; insertAt-zero-extend
    ; evalTerm-lift
    ; evalFormula-lift
    ; evalTerm-substAt
    ; evalFormula-substAt
    )
