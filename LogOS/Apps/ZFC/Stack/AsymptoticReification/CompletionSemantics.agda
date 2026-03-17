{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionSemantics where

-- Realised same-stage semantics obtained from an explicit completion witness.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as Canonical
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionWitness as Witness
import LogOS.Apps.ZFC.Proof.Semantics.Core as SemCore
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

module Complete
  {ℓ : Level}
  {C : ZF.SetContext {ℓ}}
  (K : Canonical.CanonicalRung C)
  (W : Witness.CompletionWitness K)
  where

  module R = Canonical.CanonicalRung K
  module CW = Witness.CompletionWitness W
  module Impl = R.Base.WithFO (CW.foWitnesses) (CW.wfMem)

  reifiedZFCFO = Impl.reifiedZFCFO (CW.structural)
  baseᵂ = Impl.baseᵂ (CW.structural)
  stackFO₋Fnd = Impl.stackFO₋Fnd (CW.structural)
  stackFO = Impl.stackFO (CW.structural)

  proofModel : SemCore.Model {ℓ}
  proofModel = Impl.proofModel (CW.structural)
