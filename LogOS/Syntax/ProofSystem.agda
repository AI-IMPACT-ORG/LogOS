{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Syntax.ProofSystem where

-- A small, reusable proof-system interface:
-- proofs are explicit witnesses, and validity is mediated by a decidable checker.
--
-- This lives in `Syntax` (core layer) so it can be reused by ports/adapters and
-- application packs without creating import-layer violations.
--
-- Note: universe lifts (`Lift`) that appear in tool transports are bookkeeping
-- only; they do not add logical strength or semantic content.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

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

Prov
  : ∀ {ℓI ℓP ℓW}
    {Input : Set ℓI}
    {P : Input → Set ℓP}
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

-- ---------------------------------------------------------------------------
-- Small generic transports for proof-carrying tool interfaces.
-- ---------------------------------------------------------------------------

pullback
  : ∀ {ℓI₁ ℓI₂ ℓP ℓW : Level}
    {Input₁ : Set ℓI₁}
    {Input₂ : Set ℓI₂}
    {P₂ : Input₂ → Set ℓP}
  → (f : Input₁ → Input₂)
  → ProofSystem {ℓI = ℓI₂} {ℓP = ℓP} {ℓW = ℓW} Input₂ P₂
  → ProofSystem {ℓI = ℓI₁} {ℓP = ℓP} {ℓW = ℓW} Input₁ (λ x → P₂ (f x))
pullback f PS₂ =
  record
    { Proof    = λ x → Proof PS₂ (f x)
    ; Check    = λ x pr → Check PS₂ (f x) pr
    ; decCheck = λ x pr → decCheck PS₂ (f x) pr
    ; sound    = λ x pr ok → sound PS₂ (f x) pr ok
    }

liftProofSystem
  : ∀ {ℓI ℓP ℓW ℓLift : Level}
    {Input : Set ℓI}
    {P : Input → Set ℓP}
  → ProofSystem {ℓI = ℓI} {ℓP = ℓP} {ℓW = ℓW} Input P
  → ProofSystem {ℓI = ℓI} {ℓP = ℓP ⊔ ℓLift} {ℓW = ℓW} Input (λ x → Lift ℓLift (P x))
liftProofSystem {ℓLift = ℓLift} PS =
  record
    { Proof    = Proof PS
    ; Check    = λ x pr → Lift ℓLift (Check PS x pr)
    ; decCheck = decCheck'
    ; sound    = λ x pr ok → lift (sound PS x pr (Lift.lower ok))
    }
  where
    decCheck'
      : ∀ x pr
      → Lift ℓLift (Check PS x pr)
          ⊎
        ¬ Lift ℓLift (Check PS x pr)
    decCheck' x pr with decCheck PS x pr
    ... | inj₁ ok    = inj₁ (lift ok)
    ... | inj₂ notOk = inj₂ (λ ok → notOk (Lift.lower ok))
