{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.FirstProof.Experimental.QuestionScaffold where

-- Generic scaffold for assumption-first, trace-driven question packs.

open import LogOS.Prelude

import LogOS.Theorems.Meta.QuartetCore as Quartet

record Question (ℓA ℓT ℓC : Level) : Set (lsuc (ℓA ⊔ ℓT ⊔ ℓC)) where
  field
    Assumptions : Set ℓA
    Trace       : Assumptions → Set ℓT
    Claim       : Assumptions → Set ℓC
    derive      : (A : Assumptions) → Trace A → Claim A

module Build {ℓA ℓT ℓC : Level} (Q : Question ℓA ℓT ℓC) where
  open Question Q

  record Inputs : Set (ℓA ⊔ ℓT) where
    field
      assumptions : Assumptions
      trace       : Trace assumptions

  ClaimAt : Inputs → Set ℓC
  ClaimAt I = Claim (Inputs.assumptions I)

  deriveAt : (I : Inputs) → ClaimAt I
  deriveAt I = derive (Inputs.assumptions I) (Inputs.trace I)

  module Q = Quartet.Make Inputs ClaimAt
  open Q public using (Pack; assumptionsOf; claimOf)

  mkPack : Inputs → Pack
  mkPack = Q.mkPack deriveAt
