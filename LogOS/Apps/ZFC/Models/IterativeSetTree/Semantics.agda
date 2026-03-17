{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.Semantics where

-- Curated downstream semantic entrypoint for the iterative-tree ZFC ladder.
--
-- Public surface:
-- - stage-local assumption types (`Base.ExtensionalCollapseᵛ`, `Base.StageAssumptionsᵛ`),
-- - stage-level semantic entries for hierarchy sections (`Base.StageSemanticsᵛ`),
-- - the coherent hierarchy section type (`Base.HierarchySectionᵛ`),
-- The heavier canonical/completion facades live in the sibling modules
-- `SemanticsCanonical` and `SemanticsCompletion`.

import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsStage
import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCanonical as Canonical
import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCurrentCompletionSemantics as CurrentCompletion
open import LogOS.Prelude using (Level)

module Base = LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsStage

module Curated
  (H : Base.HierarchySectionᵛ)
  {ℓ : Level}
  where

  module S = Canonical.ForLevel H {ℓ}
  module C = CurrentCompletion.ForLevel H {ℓ}

  open S public using
    ( currentBase
    ; successorBase
    )

  module Current (A : C.CurrentCompletion) where
    module M = C.CompleteCurrent A

    currentStackFO = M.stackFO
    currentModel = M.proofModel
