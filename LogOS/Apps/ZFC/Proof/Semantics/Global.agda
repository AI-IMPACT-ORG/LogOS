{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Global where

open import LogOS.Prelude using (Level; lsuc; Σ; _,_)
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.Presentation using
  ( Presentation
  ; CompletePresentation
  ; presentation↔canonical
  )
open import LogOS.LT.Derivability using (DerivationSystem)
open import LogOS.LT.Presentation.ObservationInitiality using
  ( ProbeSuite
  ; suiteView
  ; _⊑⟦_⟧_
  ; suitePresentation
  ; suiteDerivationSystem
  ; canonicalSuitePresentation
  ; canonicalSuiteComplete
  ; canonicalSuiteDerivationSystem
  )

import LogOS.Apps.ZFC.Proof.Syntax as Syntax
open Syntax
open import LogOS.Apps.ZFC.Proof.Axioms using (TheoryAxiom; axLogic; axAndElimL)
import LogOS.Apps.ZFC.Proof.System as Sys

import LogOS.Apps.ZFC.Proof.Semantics.Core as Core
import LogOS.Apps.ZFC.Proof.Semantics.Soundness as Soundness

-- Global semantics (relative to the first-order notion of model).
--
-- Quantify over all `Model`s and all valuations in each model. This gives the
-- usual “valid in all models” reading, but restricted to the record `Model`
-- above (an explicit first-order ZFC pack).

Index : ∀ {ℓ : Level} → Set (lsuc ℓ)
Index {ℓ} = Σ (Core.Model {ℓ}) (λ M → Core.Model.Valuation M)

globalSuite : ∀ {ℓ : Level} → ProbeSuite Formula (Index {ℓ}) (Sys.TruthPreorder {ℓ})
globalSuite {ℓ} =
  Sys.truthProbeSuite
    (λ where
      (M , ρ) → Soundness.ModelSoundness.evalAt M ρ)

Entails : ∀ {ℓ : Level} → Formula → Formula → Set (lsuc ℓ)
Entails {ℓ} Γ φ = Γ ⊑⟦ globalSuite {ℓ} ⟧ φ

Valid : ∀ {ℓ : Level} → Formula → Set (lsuc ℓ)
Valid {ℓ} φ = Entails {ℓ} ⊤F φ

canonicalPresentationGlobal : ∀ {ℓ : Level} → Presentation (suiteView (globalSuite {ℓ}))
canonicalPresentationGlobal {ℓ} = canonicalSuitePresentation (globalSuite {ℓ})

completePresentationGlobal : ∀ {ℓ : Level} → CompletePresentation (canonicalPresentationGlobal {ℓ})
completePresentationGlobal {ℓ} = canonicalSuiteComplete (globalSuite {ℓ})

canonicalDerivationSystemGlobal : ∀ {ℓ : Level} → DerivationSystem (suiteView (globalSuite {ℓ}))
canonicalDerivationSystemGlobal {ℓ} =
  canonicalSuiteDerivationSystem (globalSuite {ℓ}) ⊤F

soundDerivationGlobal
  : ∀ {ℓ : Level} {Γ φ}
  → Sys.Derives TheoryAxiom Γ φ
  → Entails {ℓ} Γ φ
soundDerivationGlobal d (M , ρ) =
  Soundness.ModelSoundness.soundDerivation M {ρ = ρ} d

derivesPresentationGlobal : ∀ {ℓ : Level} → Presentation (suiteView (globalSuite {ℓ}))
derivesPresentationGlobal {ℓ} =
  suitePresentation
    (globalSuite {ℓ})
    (Sys.Derives TheoryAxiom)
    Sys.hyp
    Sys.cut
    soundDerivationGlobal

derivesDerivationSystemGlobal : ∀ {ℓ : Level} → DerivationSystem (suiteView (globalSuite {ℓ}))
derivesDerivationSystemGlobal {ℓ} =
  suiteDerivationSystem
    (globalSuite {ℓ})
    (Sys.Derives TheoryAxiom)
    Sys.hyp
    Sys.cut
    soundDerivationGlobal
    ⊤F

derives↔Entails
  : ∀ {ℓ : Level}
  → CompletePresentation (derivesPresentationGlobal {ℓ})
  → ∀ {Γ φ}
  → Sys.Derives TheoryAxiom Γ φ ↔ Entails {ℓ} Γ φ
derives↔Entails C = presentation↔canonical (derivesPresentationGlobal) C

-- ------------------------------------------------------------------------
-- Consistency checks for the explicit Hilbert layer.
--
-- `LogicEqAxiom` includes a minimal propositional core (⊥, ∧, ∨, ↔) as
-- explicit axioms, keeping `Proof.System` rule-minimal (modus ponens).
--
-- Soundness transports these axioms into the intended model semantics.

∧-proj-valid
  : ∀ {ℓ : Level} (A B : Formula)
  → Valid {ℓ} ((A ∧F B) ⇒ A)
∧-proj-valid A B (M , ρ) _ (a , _) = a

∧-proj-theorem
  : ∀ (A B : Formula)
  → Sys.Theorem TheoryAxiom ((A ∧F B) ⇒ A)
∧-proj-theorem A B = Sys.axiom (axLogic (axAndElimL A B))
