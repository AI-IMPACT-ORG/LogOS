{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.ObservationEvaluation where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.ConPreorder.Truth using (TruthPreorder; truthView)
open import LogOS.LT.View using (_⊑[_]_)
open import LogOS.LT.Presentation using
  ( Presentation
  ; CompletePresentation
  ; presentation↔canonical
  )
open import LogOS.LT.Presentation.Independence using (presentationsAgree)
open import LogOS.LT.Derivability using (DerivationSystem)
open import LogOS.LT.Presentation.ObservationInitiality using
  ( ProbeSuite
  ; DependentProbeSuite
  ; probe
  ; suiteView
  ; suitePresentation
  ; suiteDerivationSystem
  ; canonicalSuitePresentation
  ; canonicalSuiteComplete
  ; canonicalSuiteDerivationSystem
  ; _⊑⟦_⟧_
  ; _⊑⟦_⟧ᵈ_
  ; toDependentProbeSuite
  ; suiteDerivationSystemᵈ
  )

data Carrier : Set where
  α β : Carrier

data ProbeIx : Set where
  left right : ProbeIx

toySuite : ProbeSuite Carrier ProbeIx (TruthPreorder {lzero})
toySuite =
  record
    { probe = λ where
        left  → truthView leftObs
        right → truthView rightObs
    }
  where
    leftObs : Carrier → Set
    leftObs α = ⊤
    leftObs β = ⊥

    rightObs : Carrier → Set
    rightObs α = ⊤
    rightObs β = ⊤

infix 4 _≼toy_
data _≼toy_ : Carrier → Carrier → Set where
  reflα : α ≼toy α
  reflβ : β ≼toy β
  β≤α   : β ≼toy α

reflToy : ∀ {x} → x ≼toy x
reflToy {α} = reflα
reflToy {β} = reflβ

transToy : ∀ {a b c} → a ≼toy b → b ≼toy c → a ≼toy c
transToy reflα q = q
transToy reflβ reflβ = reflβ
transToy reflβ β≤α = β≤α
transToy β≤α reflα = β≤α

soundToy
  : ∀ {x y}
  → x ≼toy y
  → ∀ i → x ⊑[ probe toySuite i ] y
soundToy reflα left p = p
soundToy reflα right p = p
soundToy reflβ left p = p
soundToy reflβ right p = p
soundToy β≤α left ()
soundToy β≤α right p = p

toyPresentation : Presentation (suiteView toySuite)
toyPresentation =
  suitePresentation toySuite _≼toy_ reflToy transToy soundToy

toyDerivationSystem : DerivationSystem (suiteView toySuite)
toyDerivationSystem =
  suiteDerivationSystem toySuite _≼toy_ reflToy transToy soundToy β

module ToyDS = DerivationSystem toyDerivationSystem

β⊑suiteα : β ⊑⟦ toySuite ⟧ α
β⊑suiteα = ToyDS.derivable-sound β≤α

toyDependentSuite : DependentProbeSuite Carrier ProbeIx (λ _ → TruthPreorder {lzero})
toyDependentSuite = toDependentProbeSuite toySuite

soundToyᵈ
  : ∀ {x y}
  → x ≼toy y
  → ∀ i → x ⊑[ probe toyDependentSuite i ] y
soundToyᵈ le i = soundToy le i

toyDerivationSystemᵈ
  : DerivationSystem
      (LogOS.LT.Presentation.ObservationInitiality.suiteViewᵈ toyDependentSuite)
toyDerivationSystemᵈ =
  suiteDerivationSystemᵈ toyDependentSuite _≼toy_ reflToy transToy soundToyᵈ β

module ToyDSᵈ = DerivationSystem toyDerivationSystemᵈ

β⊑suiteαᵈ : β ⊑⟦ toyDependentSuite ⟧ᵈ α
β⊑suiteαᵈ = ToyDSᵈ.derivable-sound β≤α

toyCanonicalPresentation : Presentation (suiteView toySuite)
toyCanonicalPresentation = canonicalSuitePresentation toySuite

toyCanonicalComplete : CompletePresentation toyCanonicalPresentation
toyCanonicalComplete = canonicalSuiteComplete toySuite

toyCanonicalDerivationSystem : DerivationSystem (suiteView toySuite)
toyCanonicalDerivationSystem = canonicalSuiteDerivationSystem toySuite β

toyComplete : CompletePresentation toyPresentation
toyComplete =
  record
    { fromCanonical = fromCanonicalToy
    }
  where
    fromCanonicalToy : ∀ {x y} → x ⊑⟦ toySuite ⟧ y → x ≼toy y
    fromCanonicalToy {α} {α} _ = reflα
    fromCanonicalToy {α} {β} le with le left tt
    ... | ()
    fromCanonicalToy {β} {α} _ = β≤α
    fromCanonicalToy {β} {β} _ = reflβ

canonical↔suite
  : ∀ {x y}
  → Presentation._≼_ toyCanonicalPresentation x y ↔ x ⊑⟦ toySuite ⟧ y
canonical↔suite =
  presentation↔canonical toyCanonicalPresentation toyCanonicalComplete

manual↔canonical
  : ∀ {x y}
  → Presentation._≼_ toyPresentation x y
  ↔ Presentation._≼_ toyCanonicalPresentation x y
manual↔canonical =
  presentationsAgree toyPresentation toyCanonicalPresentation toyComplete toyCanonicalComplete

_ : Presentation (suiteView toySuite)
_ = toyPresentation

_ : DerivationSystem (suiteView toySuite)
_ = toyCanonicalDerivationSystem
