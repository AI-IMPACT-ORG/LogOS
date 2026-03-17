{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Core.LiftSubst where

open import LogOS.Prelude using (Level)
open import LogOS.Apps.ZFC.Proof.Semantics.Core.ModelDef using (Model)
import LogOS.Apps.ZFC.Proof.Semantics.Core.SubstReasoning as SubstReasoning

module ForModel {ℓ : Level} (M : Model {ℓ}) where
  open SubstReasoning.ForModel M public using
    ( ↔-trans
    ; ValEq
    ; extend-cong
    ; evalFormula-cong
    ; evalFormula-rename
    ; tailVal
    ; insertAt
    ; insertAt-suc-extend
    ; insertAt-zero-extend
    ; evalTerm-lift
    ; evalFormula-lift
    ; evalTerm-substAt
    ; evalFormula-substAt
    )
