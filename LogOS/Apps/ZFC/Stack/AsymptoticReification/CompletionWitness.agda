{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.CompletionWitness where

-- Explicit same-stage completion witness layered over a canonical rung.
--
-- This module packages only the witness data required to realise same-stage
-- semantics. The realised semantics themselves live in `CompletionSemantics`.

open import LogOS.Prelude

import LogOS.Apps.ZFC.Stack.AsymptoticReification.CanonicalRung as Canonical
import LogOS.Apps.ZFC.Stack.ZFCore as ZF

record CompletionWitness
  {ℓ : Level}
  {C : ZF.SetContext {ℓ}}
  (K : Canonical.CanonicalRung C)
  : Set (lsuc (lsuc ℓ)) where

  module R = Canonical.CanonicalRung K

  field
    foWitnesses : R.FOWitnesses
    wfMem : R.WFMem
    structural : R.StructuralAssumptions

open CompletionWitness public
