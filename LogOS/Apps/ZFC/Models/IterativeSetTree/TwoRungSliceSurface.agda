{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree.TwoRungSliceSurface where

open import LogOS.Prelude using (Level)

import LogOS.Apps.ZFC.Models.IterativeSetTree.Semantics
import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCurrentCompletionSemantics
import LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsSuccessorCompletionSemantics

module Base = LogOS.Apps.ZFC.Models.IterativeSetTree.Semantics.Base

module TwoRungSlice
  (H : Base.HierarchySectionᵛ)
  {ℓ : Level}
  where

  module C0 = LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsCurrentCompletionSemantics.ForLevel H {ℓ}
  module C1 = LogOS.Apps.ZFC.Models.IterativeSetTree.SemanticsSuccessorCompletionSemantics.ForLevel H {ℓ}

  module Current (A : C0.CurrentCompletion) where
    module M = C0.CompleteCurrent A

    currentModel = M.proofModel
    currentStackFO = M.stackFO

  module Successor (A : C1.SuccessorCompletion) where
    module M = C1.CompleteSuccessor A

    successorModel = M.proofModel
    successorStackFO = M.stackFO
