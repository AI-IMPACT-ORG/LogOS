{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ProofSystem where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_)

-- A small, reusable proof-system interface:
-- proofs are explicit witnesses, and validity is mediated by a decidable checker.

record ProofSystem {ℓI ℓP ℓW : Level}
                   (Input : Set ℓI)
                   (P     : Input → Set ℓP)
                   : Set (lsuc (lsuc (ℓI ⊔ ℓP ⊔ ℓW))) where
  field
    Proof    : Input → Set ℓW
    Check    : ∀ x → Proof x → Set ℓP
    decCheck : ∀ x p → Check x p ⊎ ¬ Check x p
    sound    : ∀ x p → Check x p → P x

open ProofSystem public

Prov : ∀ {ℓI ℓP ℓW} {Input : Set ℓI} {P : Input → Set ℓP}
       → ProofSystem {ℓI = ℓI} {ℓP = ℓP} {ℓW = ℓW} Input P
       → Input → Set (ℓP ⊔ ℓW)
Prov PS x = Σ (Proof PS x) (λ p → Check PS x p)

record Complete {ℓI ℓP ℓW : Level}
                {Input : Set ℓI}
                {P : Input → Set ℓP}
                (PS : ProofSystem {ℓI = ℓI} {ℓP = ℓP} {ℓW = ℓW} Input P)
                : Set (lsuc (lsuc (ℓI ⊔ ℓP ⊔ ℓW))) where
  field
    complete : ∀ x → P x → Prov PS x
