{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionLayer where

-- Same-stage semantic completion layered over a canonical rung.
--
-- This is intentionally separate from the canonical hierarchy transport:
-- the rung is canonical; FO witnesses / well-foundedness / structural upgrades
-- remain explicit decoration.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as Canonical
import LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionWitness as Witness
import LogOS.Apps.ZFC.Proof.Semantics.Core as SemCore
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

record CompletionLayer
  {ℓ : Level}
  {C : ZF.SetContext {ℓ}}
  (K : Canonical.CanonicalRung C)
  : Set (lsuc (lsuc ℓ)) where

  module R = Canonical.CanonicalRung K

  field
    foWitnesses : R.FOWitnesses
    wfMem : R.WFMem
    structural : R.StructuralAssumptions

  module Complete = R.Base.WithFO foWitnesses wfMem

  reifiedZFCFO = Complete.reifiedZFCFO structural
  baseᵂ = Complete.baseᵂ structural
  stackFO₋Fnd = Complete.stackFO₋Fnd structural
  stackFO = Complete.stackFO structural

  proofModel : SemCore.Model {ℓ}
  proofModel = Complete.proofModel structural

open CompletionLayer public

fromWitness
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}} {K : Canonical.CanonicalRung C}
  -> Witness.CompletionWitness K
  -> CompletionLayer K
fromWitness W =
  let
    module CW = Witness.CompletionWitness W
  in
  record
    { foWitnesses = CW.foWitnesses
    ; wfMem = CW.wfMem
    ; structural = CW.structural
    }
