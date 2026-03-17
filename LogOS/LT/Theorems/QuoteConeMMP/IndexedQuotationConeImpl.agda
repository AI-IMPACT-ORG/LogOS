{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.QuoteConeMMP.IndexedQuotationConeImpl where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Indexed variant (general): contextual approximation on quotation witnesses.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_)
open import LogOS.LT.ConPreorder.Indexed using (IndexedConPreorder; mkIndexedConPreorder)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Kernel using (Kernel; bnd; decode; EncodePort; encode)
import LogOS.LT.Theorems.Centering as Centering

module IndexedQuotationCone
  {ℓ ℓRel ℓCode ℓI ℓAt : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (GC₀ : GuardedClosure (bnd K))
  (Context : Set ℓI)
  (AtICP : IndexedConPreorder Context (Con (bnd K)) ℓAt)
  where

  infix 4 _⊑At_ _≈At_
  _⊑At_ : Context → Con (bnd K) → Con (bnd K) → Set ℓAt
  _⊑At_ = IndexedConPreorder._⊑_ AtICP

  _≈At_ : Context → Con (bnd K) → Con (bnd K) → Set ℓAt
  _≈At_ = IndexedConPreorder._≈_ AtICP

  -- Candidate: encoders that realise quotation up to the fixed closure GC₀,
  -- uniformly at every index.
  record QuoteWitnessᵢ : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode ⊔ ℓI ⊔ ℓAt)) where
    field
      EK : EncodePort K
      decode-encode≈FlowAt
        : ∀ i c
        → _≈At_ i (decode K (encode EK c)) (GuardedClosure.Flow GC₀ c)

  open QuoteWitnessᵢ public

  -- Observation of a witness: its boundary meaning as a function.
  obs : QuoteWitnessᵢ → Con (bnd K) → Con (bnd K)
  obs R c = decode K (encode (QuoteWitnessᵢ.EK R) c)

  infix 4 _⊑RAt_
  _⊑RAt_ : Context → QuoteWitnessᵢ → QuoteWitnessᵢ → Set (ℓ ⊔ ℓAt)
  _⊑RAt_ ctx R S = ∀ c → _⊑At_ ctx (obs R c) (obs S c)

  reflRAt : ∀ {ctx R} → _⊑RAt_ ctx R R
  reflRAt {ctx} {R} c =
    IndexedConPreorder.reflAt AtICP {i = ctx} {x = obs R c}

  transRAt
    : ∀ {ctx R S T}
    → _⊑RAt_ ctx R S
    → _⊑RAt_ ctx S T
    → _⊑RAt_ ctx R T
  transRAt {ctx} rs st c =
    IndexedConPreorder.transAt AtICP {i = ctx} (rs c) (st c)

  RAtICP : IndexedConPreorder Context QuoteWitnessᵢ (ℓ ⊔ ℓAt)
  RAtICP =
    mkIndexedConPreorder _⊑RAt_
      (λ {ctx} {R} → reflRAt {ctx = ctx} {R = R})
      (λ {ctx} {R} {S} {T} rs st → transRAt {ctx = ctx} {R = R} {S = S} {T = T} rs st)

  to
    : (ctx : Context)
    → (R S : QuoteWitnessᵢ)
    → ∀ c → _⊑At_ ctx (obs R c) (obs S c)
  to ctx R S c =
    IndexedConPreorder.sandwichAt AtICP
      (decode-encode≈FlowAt R ctx c)
      (decode-encode≈FlowAt S ctx c)

  fiberAt
    : (canonical : QuoteWitnessᵢ)
    → Centering.IndexedContractibleFiber Context QuoteWitnessᵢ (IndexedConPreorder._≈_ RAtICP)
  fiberAt canonical =
    Centering.mkIndexedConPreorderContractibleFiber
      RAtICP
      canonical
      (λ i R → (to i R canonical , to i canonical R))
