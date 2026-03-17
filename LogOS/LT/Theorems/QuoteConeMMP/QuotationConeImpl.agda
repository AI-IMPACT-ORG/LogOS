{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theorems.QuoteConeMMP.QuotationConeImpl where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Packaging as a cone theorem over the carrier “quotation witnesses”.
--
-- Relation is extensional: compare witnesses only by their induced boundary
-- behaviour (`decode ∘ encode`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; _≈_
  ; ≈-sym
  ; sandwich⊑
  )
open import LogOS.LT.FunPreorder using (FunPreorder)
open import LogOS.LT.View using (View; μ; PullbackPreorder)
open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Kernel using (Kernel; bnd; decode; EncodePort; encode)
import LogOS.LT.Theorems.Centering as Centering

module QuotationCone
  {ℓ ℓRel ℓCode : Level}
  (K : Kernel ℓ ℓRel ℓCode)
  (GC₀ : GuardedClosure (bnd K))
  where

  -- Candidate: encoders that realise quotation up to the fixed closure GC₀.
  record QuoteWitness : Set (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode)) where
    field
      EK : EncodePort K
      decode-encode≈Flow : ∀ c → _≈_ (bnd K) (decode K (encode EK c)) (GuardedClosure.Flow GC₀ c)

  open QuoteWitness public

  -- Observation of a witness: its boundary meaning as a function.
  obs : QuoteWitness → Con (bnd K) → Con (bnd K)
  obs R c = decode K (encode (QuoteWitness.EK R) c)

  obsView : View QuoteWitness (FunPreorder (Con (bnd K)) (bnd K))
  obsView = record { μ = obs }

  QuoteWitnessPreorder : ConPreorder _ _
  QuoteWitnessPreorder = PullbackPreorder obsView

  infix 4 _≈R_
  _≈R_ : QuoteWitness → QuoteWitness → Set (ℓ ⊔ ℓRel)
  _≈R_ = _≈_ QuoteWitnessPreorder

  contractTo
    : (canonical : QuoteWitness)
    → ∀ R
    → _≈R_ R canonical
  contractTo canonical R =
    (to R canonical , to canonical R)
    where
      to : (R S : QuoteWitness) → ∀ c → _⊑_ (bnd K) (obs R c) (obs S c)
      to R S c =
        sandwich⊑
          {CP = bnd K}
          (decode-encode≈Flow R c)
          (decode-encode≈Flow S c)

  fiber
    : (canonical : QuoteWitness)
    → Centering.ContractibleFiber QuoteWitness _≈R_
  fiber canonical =
    Centering.mkConPreorderContractibleFiber
      QuoteWitnessPreorder
      canonical
      (contractTo canonical)
