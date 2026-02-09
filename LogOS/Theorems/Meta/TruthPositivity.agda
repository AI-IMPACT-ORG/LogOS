{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.TruthPositivity where

open import LogOS.Prelude
open import LogOS.Prelude using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude using (_⊎_; inj₁; inj₂)

-- A tiny meta-meta interface for “truth positivity”:
-- there is a space of tests, a positivity predicate, and a class of observable
-- tests on which positivity holds.
--
-- This is intentionally logic-agnostic: it lives at the meta level and can be
-- instantiated by code-level partial evaluators (Rice/Gödel barriers force these
-- to be partial in reflective settings), or by model-level semantics.

record TruthPositivity {ℓT ℓW ℓObs : Level} : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  field
    Test       : Set ℓT
    W-pos      : Test → Set ℓW
    Observable : Test → Set ℓObs
    positivity : ∀ t → Observable t → W-pos t

-- A generic partial-output surface for a predicate P on tests:
-- return either a positive witness (inj₁) or explicitly “undefined” (inj₂ tt).

record PartialWitness {ℓT ℓW : Level}
                      (Test  : Set ℓT)
                      (W-pos : Test → Set ℓW)
                      : Set (lsuc (ℓT ⊔ ℓW)) where
  field
    infer : Test → (Σ Test W-pos) ⊎ ⊤ {ℓ = lzero}

  Observable : Test → Set (ℓT ⊔ ℓW)
  Observable t = Σ (W-pos t) (λ p → infer t ≡ inj₁ (t , p))

  positivity : ∀ t → Observable t → W-pos t
  positivity t obs = proj₁ obs

-- Build a TruthPositivity instance directly from a partial witness surface.

fromPartialWitness
  : ∀ {ℓT ℓW}
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW : PartialWitness Test W-pos)
  → TruthPositivity {ℓT} {ℓW} {ℓT ⊔ ℓW}
fromPartialWitness {Test = Test} {W-pos = W-pos} PW = record
  { Test       = Test
  ; W-pos      = W-pos
  ; Observable = PartialWitness.Observable PW
  ; positivity = PartialWitness.positivity PW
  }

-- A proof/certificate surface: a checkable object witnessing positivity.
-- This matches “Metamath-style” observability: proofs are finite objects and
-- checking them yields a concrete positivity witness.

record ProofWitness {ℓT ℓW ℓP : Level}
                    (Test  : Set ℓT)
                    (W-pos : Test → Set ℓW)
                    : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓP)) where
  field
    Proof : Test → Set ℓP
    check : ∀ {t} → Proof t → W-pos t

  Observable : Test → Set ℓP
  Observable = Proof

  positivity : ∀ t → Observable t → W-pos t
  positivity _ p = check p

fromProofWitness
  : ∀ {ℓT ℓW ℓP}
    {Test : Set ℓT}
    {W-pos : Test → Set ℓW}
    (PW : ProofWitness {ℓP = ℓP} Test W-pos)
  → TruthPositivity {ℓT} {ℓW} {ℓP}
fromProofWitness {Test = Test} {W-pos = W-pos} PW = record
  { Test       = Test
  ; W-pos      = W-pos
  ; Observable = ProofWitness.Observable PW
  ; positivity = ProofWitness.positivity PW
  }
