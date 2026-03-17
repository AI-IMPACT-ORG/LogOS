{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.System where

open import LogOS.Prelude using (Level; lsuc)
open import LogOS.LT.ConPreorder using (ConPreorder)
import LogOS.LT.ConPreorder.Truth as Truth
open import LogOS.LT.View using (View)
open import LogOS.LT.Presentation using (Presentation) renaming (canonicalPresentation to canonicalPresentationV)
open import LogOS.LT.Derivability using (DerivationSystem) renaming (canonicalDerivationSystem to canonicalDerivationSystemV)
open import LogOS.LT.Presentation.ObservationInitiality using (ProbeSuite)
import LogOS.LT.Theory as LTTheory
open import LogOS.Apps.ZFC.Proof.Syntax using (Formula; _⇒_; ⊤F)

TruthPreorder : ∀ {ℓ : Level} → ConPreorder (lsuc ℓ) ℓ
TruthPreorder = Truth.TruthPreorder

truthView : ∀ {ℓX ℓ : Level} {X : Set ℓX} → (X → Set ℓ) → View X (TruthPreorder {ℓ})
truthView = Truth.truthView

truthProbeSuite
  : ∀ {ℓX ℓI ℓ : Level}
    {X : Set ℓX}
    {I : Set ℓI}
  → (I → X → Set ℓ)
  → ProbeSuite X I (TruthPreorder {ℓ})
truthProbeSuite evalAt =
  record
    { probe = λ i → truthView (evalAt i)
    }

data Derives (Ax : Formula → Set) : Formula → Formula → Set where
  hyp   : ∀ {Γ} → Derives Ax Γ Γ
  axiom : ∀ {Γ φ} → Ax φ → Derives Ax Γ φ
  mp    : ∀ {Γ φ ψ} → Derives Ax Γ (φ ⇒ ψ) → Derives Ax Γ φ → Derives Ax Γ ψ
  cut   : ∀ {Γ φ ψ} → Derives Ax Γ φ → Derives Ax φ ψ → Derives Ax Γ ψ

-- Canonical derivability: take semantic entailment itself as the preorder.
--
-- This gives a proof layer that is complete-by-construction for any chosen evaluation function
-- (derivability is semantic entailment),
-- without postulating any additional axioms or inference rules.
CanonicalDerives : ∀ {ℓ : Level} → (Formula → Set ℓ) → Formula → Formula → Set ℓ
CanonicalDerives eval Γ φ = eval Γ → eval φ

sound
  : ∀ {ℓ : Level} {Ax : Formula → Set}
  → (eval : Formula → Set ℓ)
  → (imp-elim : ∀ {φ ψ} → eval (φ ⇒ ψ) → eval φ → eval ψ)
  → (axiomSound : ∀ {φ} → Ax φ → eval φ)
  → ∀ {Γ φ} → Derives Ax Γ φ → eval Γ → eval φ
sound eval imp-elim axiomSound hyp g = g
sound eval imp-elim axiomSound (axiom a) _ = axiomSound a
sound eval imp-elim axiomSound (mp dImp dArg) g =
  imp-elim (sound eval imp-elim axiomSound dImp g)
           (sound eval imp-elim axiomSound dArg g)
sound eval imp-elim axiomSound (cut d₁ d₂) g =
  sound eval imp-elim axiomSound d₂ (sound eval imp-elim axiomSound d₁ g)

private
  module EvaluatorPackaging
    {ℓ : Level}
    {Ax : Formula → Set}
    (eval : Formula → Set ℓ)
    (imp-elim : ∀ {φ ψ} → eval (φ ⇒ ψ) → eval φ → eval ψ)
    (axiomSound : ∀ {φ} → Ax φ → eval φ)
    where

    presentation
      : Presentation (Truth.truthView eval)
    presentation =
      record
        { _≼_ = Derives Ax
        ; refl≼ = hyp
        ; trans≼ = cut
        ; observe-mono = sound eval imp-elim axiomSound
        }

    derivationSystem
      : DerivationSystem (Truth.truthView eval)
    derivationSystem =
      record
        { presentation = presentation
        ; base = ⊤F
        }

presentation
  : ∀ {ℓ : Level} {Ax : Formula → Set}
  → (eval : Formula → Set ℓ)
  → (imp-elim : ∀ {φ ψ} → eval (φ ⇒ ψ) → eval φ → eval ψ)
  → (axiomSound : ∀ {φ} → Ax φ → eval φ)
  → Presentation (Truth.truthView eval)
presentation eval imp-elim axiomSound =
  EvaluatorPackaging.presentation eval imp-elim axiomSound

derivationSystem
  : ∀ {ℓ : Level} {Ax : Formula → Set}
  → (eval : Formula → Set ℓ)
  → (imp-elim : ∀ {φ ψ} → eval (φ ⇒ ψ) → eval φ → eval ψ)
  → (axiomSound : ∀ {φ} → Ax φ → eval φ)
  → DerivationSystem (Truth.truthView eval)
derivationSystem eval imp-elim axiomSound =
  EvaluatorPackaging.derivationSystem eval imp-elim axiomSound

canonicalPresentation : ∀ {ℓ : Level} → (eval : Formula → Set ℓ) → Presentation (Truth.truthView eval)
canonicalPresentation eval = canonicalPresentationV (Truth.truthView eval)

canonicalDerivationSystem : ∀ {ℓ : Level} → (eval : Formula → Set ℓ) → DerivationSystem (Truth.truthView eval)
canonicalDerivationSystem eval = canonicalDerivationSystemV (Truth.truthView eval) ⊤F

Theorem : (Formula → Set) → Formula → Set
Theorem Ax φ = Derives Ax ⊤F φ

CanonicalTheorem : ∀ {ℓ : Level} → (Formula → Set ℓ) → Formula → Set ℓ
CanonicalTheorem eval φ = CanonicalDerives eval ⊤F φ

theorem-sound
  : ∀ {ℓ : Level} {Ax : Formula → Set}
  → (eval : Formula → Set ℓ)
  → (imp-elim : ∀ {φ ψ} → eval (φ ⇒ ψ) → eval φ → eval ψ)
  → (axiomSound : ∀ {φ} → Ax φ → eval φ)
  → (baseSound : eval ⊤F)
  → ∀ {φ} → Theorem Ax φ → eval φ
theorem-sound eval imp-elim axiomSound baseSound d =
  sound eval imp-elim axiomSound d baseSound

canonicalTheorem-sound
  : ∀ {ℓ : Level}
  → (eval : Formula → Set ℓ)
  → (baseSound : eval ⊤F)
  → ∀ {φ} → CanonicalTheorem eval φ → eval φ
canonicalTheorem-sound eval baseSound d = d baseSound

-- --------------------------------------------------------------------------
-- Theories + closure (kernel re-export)

module TheoryMP = LTTheory.HilbertMP Formula _⇒_

open TheoryMP public using
  ( Theory
  ; _⊑T_
  ; TheoryPreorder
  ; DerivesT
  ; hypT
  ; axiomT
  ; mpT
  ; FlowTheory
  ; theoryClosure
  ; theoryKZ
  ; ClosedTheory
  ; closeTheory
  ; theoryOf
  ; closeTheory-eval⊑FlowTheory
  ; FlowTheory⊑closeTheory-eval
  ; closed-elim
  ; closed-intro
  )
