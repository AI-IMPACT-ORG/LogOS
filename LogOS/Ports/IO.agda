{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.IO where

-- Input/output (including telemetry) as a first-class hexagonal port.
--
-- An I/O port specifies:
-- - a space of inputs (tests, queries, environments, prompts, ...)
-- - which inputs are admissible (an interface boundary)
-- - an output observation into a chosen constraint preorder `O`
--
-- Adequacy is about whether the admissible inputs are sufficient to reflect
-- refinement of output constraints.
--
-- Polarity note:
-- `_⊑_ c d` means `d` is the stronger output constraint. The induced
-- satisfaction/entailment layer is therefore contravariant in admissible tests.
-- Where an order-flavoured public surface helps, this module uses `≼` as an
-- alias for that same refinement relation and reserves plain `≤` for
-- quantitative orders.

open import LogOS.Prelude
open LogOS.Prelude.RefinementKit using (_≼_)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
private
  module ≼-Reasoning = LogOS.Prelude.RefinementKit.Reasoning
open import LogOS.LT.View using (View; PullbackPreorder; _⊑[_]_)
open import LogOS.LT.Presentation.ObservationInitiality using (ProbeSuite; suiteView; _⊑⟦_⟧_)
open import LogOS.Syntax.Prop using (_↔_; intro)

record IOPort
  {ℓX ℓI ℓA ℓOCon ℓORel : Level}
  (X : Set ℓX)
  (I : Set ℓI)
  (O : ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓX ⊔ ℓI ⊔ ℓA ⊔ ℓOCon ⊔ ℓORel)) where
  field
    admissible : I → Set ℓA
    outputObs : I → View X O

  output : I → View X O
  output = outputObs

  IAdmissible : Set (ℓI ⊔ ℓA)
  -- Intended reading: `admissible i` is a predicate/proposition (“this input is
  -- allowed by the interface”). If it carries nontrivial proof content, then
  -- `Σ I admissible` may contain duplicates; this is harmless for the refinement
  -- relations below (they quantify over `i` and a witness of admissibility).
  IAdmissible = Σ I admissible

  suite : ProbeSuite X IAdmissible O
  suite = record { probe = λ (i , _) → outputObs i }

  ioView : View X _
  ioView = suiteView suite

  IOPreorder : ConPreorder _ _
  IOPreorder = PullbackPreorder ioView

  infix 4 _⊑io_ _≼io_ _≈io_

  _⊑io_ : X → X → Set (ℓI ⊔ ℓA ⊔ ℓORel)
  x ⊑io y = ∀ i → admissible i → x ⊑[ outputObs i ] y

  _≼io_ : X → X → Set (ℓI ⊔ ℓA ⊔ ℓORel)
  _≼io_ = _⊑io_

  _≈io_ : X → X → Set (ℓI ⊔ ℓA ⊔ ℓORel)
  _≈io_ = _≈_ IOPreorder

  ≼io↔⊑suite : ∀ {x y} → x ≼io y ↔ x ⊑⟦ suite ⟧ y
  ≼io↔⊑suite =
    intro
      (λ le (i , ai) → le i ai)
      (λ le i ai → le (i , ai))

  ⊑io↔⊑suite : ∀ {x y} → x ⊑io y ↔ x ⊑⟦ suite ⟧ y
  ⊑io↔⊑suite = ≼io↔⊑suite

uniformIOPort
  : ∀ {ℓX ℓI ℓA ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → (admissible : I → Set ℓA)
  → View X O
  → IOPort {ℓA = ℓA} X I O
uniformIOPort admissible outputObs =
  record
    { admissible = admissible
    ; outputObs = λ _ → outputObs
    }

constantAdmissibleIOPort
  : ∀ {ℓX ℓI ℓA ℓOCon ℓORel}
    {X : Set ℓX}
    {I : Set ℓI}
    {O : ConPreorder ℓOCon ℓORel}
  → Set ℓA
  → (I → View X O)
  → IOPort {ℓA = ℓA} X I O
constantAdmissibleIOPort A outputObs =
  record
    { admissible = λ _ → A
    ; outputObs = outputObs
    }

-- --------------------------------------------------------------------------
-- Adequacy kit (constraint-level): admissible inputs induce entailment.

-- Entailment induced by admissible inputs + a satisfaction predicate.
EntailsIO
  : ∀ {ℓI ℓA ℓOCon ℓORel ℓSat}
    {I : Set ℓI}
  → (O : ConPreorder ℓOCon ℓORel)
  → (admissible : I → Set ℓA)
  → (Sat : I → Con O → Set ℓSat)
  → Con O → Con O → Set (ℓI ⊔ ℓA ⊔ ℓSat)
EntailsIO O admissible Sat c d =
  ∀ i → admissible i → Sat i d → Sat i c

-- Soundness/monotonicity assumption on satisfaction:
-- refinement makes constraints *harder* to satisfy (contravariant in `⊑`).
IOSound
  : ∀ {ℓI ℓA ℓOCon ℓORel ℓSat}
    {I : Set ℓI}
  → (O : ConPreorder ℓOCon ℓORel)
  → (admissible : I → Set ℓA)
  → (Sat : I → Con O → Set ℓSat)
  → Set (ℓI ⊔ ℓA ⊔ ℓOCon ⊔ ℓORel ⊔ ℓSat)
IOSound O admissible Sat =
  ∀ {i c d} → admissible i → _≼_ O c d → Sat i d → Sat i c

sound-EntailsIO
  : ∀ {ℓI ℓA ℓOCon ℓORel ℓSat}
    {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    {admissible : I → Set ℓA}
    {Sat : I → Con O → Set ℓSat}
  → IOSound O admissible Sat
  → ∀ {c d} → _≼_ O c d → EntailsIO O admissible Sat c d
sound-EntailsIO sound le i adm satd = sound adm le satd

-- Adequacy: semantic entailment reflects back to refinement.
record IOAdequacy
  {ℓI ℓA ℓOCon ℓORel ℓSat}
  {I : Set ℓI} (O : ConPreorder ℓOCon ℓORel)
  (admissible : I → Set ℓA)
  (Sat : I → Con O → Set ℓSat)
  : Set (lsuc (ℓI ⊔ ℓA ⊔ ℓOCon ⊔ ℓORel ⊔ ℓSat)) where
  field
    reflect : ∀ {c d} → EntailsIO O admissible Sat c d → _≼_ O c d

open IOAdequacy public
-- If a smaller input interface already reflects refinement, any extension of it does as well.
extendInputs
  : ∀ {ℓI ℓA₁ ℓA₂ ℓOCon ℓORel ℓSat}
    {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    {A₁ : I → Set ℓA₁} {A₂ : I → Set ℓA₂}
    {Sat : I → Con O → Set ℓSat}
  → (∀ i → A₁ i → A₂ i)
  → IOAdequacy O A₁ Sat
  → IOAdequacy O A₂ Sat
extendInputs incl A =
  record
    { reflect = λ entails₂ →
        reflect A (λ i a₁ satd → entails₂ i (incl i a₁) satd)
    }

-- Outputs as first-class: a model is an input-indexed output constraint.
record OutputModel {ℓI ℓOCon ℓORel} (I : Set ℓI) (O : ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓI ⊔ ℓOCon ⊔ ℓORel)) where
  field
    outputs : I → Con O

open OutputModel public
ModelsOutput
  : ∀ {ℓI ℓOCon ℓORel} {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
  → OutputModel I O
  → I → Con O → Set ℓORel
ModelsOutput {O = O} M i c = _≼_ O c (outputs M i)

modelsOutput-sound
  : ∀ {ℓI ℓA ℓOCon ℓORel}
    {I : Set ℓI} {O : ConPreorder ℓOCon ℓORel}
    {admissible : I → Set ℓA}
    (M : OutputModel I O)
  → IOSound O admissible (ModelsOutput M)
modelsOutput-sound {O = O} M {i = i} {c = c} {d = d} _ le satd =
  let
    module R = ≼-Reasoning O
    open R using (begin≼_; _≼⟨_⟩_; _∎≼)
  in
  begin≼
    c ≼⟨ le ⟩
    d ≼⟨ satd ⟩
    outputs M i ∎≼
