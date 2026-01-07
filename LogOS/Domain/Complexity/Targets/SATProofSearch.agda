{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Targets.SATProofSearch where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; ↔-refl)

import LogOS.Domain.Complexity.ProofSystem as PS
import LogOS.Domain.Complexity.Targets.SAT as SAT

-- SAT as a proof-search predicate: proofs are assignments, checking is evaluation.

SATProofSystem : PS.ProofSystem SAT.CNF SAT.SAT
SATProofSystem =
  record
    { Proof    = λ _ → SAT.Assignment
    ; Check    = SAT.Check
    ; decCheck = SAT.decCheck
    ; sound    = λ φ ρ ok → ρ , ok
    }

SATProofSearch : SAT.CNF → Set
SATProofSearch = PS.Prov SATProofSystem

sat↔proofSearch : ∀ φ → SAT.SAT φ ↔ SATProofSearch φ
sat↔proofSearch _ = ↔-refl
