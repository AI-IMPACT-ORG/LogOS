{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Semantics.Soundness.Presentation where

open import LogOS.Prelude using
  ( Level
  ; _×_
  ; _⊎_
  ; Σ
  ; _,_
  ; fst
  ; snd
  ; proj₁
  ; proj₂
  ; inj₁
  ; inj₂
  ; refl
  ; sym
  ; trans
  ; cong
  ; cong₂
  ; subst
  ; ⊥-elim
  ; _≡_
  )
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.Syntax.Prop using (_↔_; intro; to; from)
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
import LogOS.Apps.ZFC.Proof.Axioms as Ax
open Ax
import LogOS.Apps.ZFC.Proof.System as Sys

import LogOS.Apps.ZFC.Proof.Semantics.Core as Core
import LogOS.Apps.ZFC.Proof.Semantics.Soundness.Logic as Logic
import LogOS.Apps.ZFC.Proof.Semantics.Soundness.ZF as ZF

module ForModel {ℓ : Level} (M : Core.Model {ℓ}) where
  open Core.Model M

  open Logic.ForModel M using (Extensionality; logicEqSound; logicEqExtSound)
  open ZF.ForModel M using (zfSound; zfcSound)

  theorySound : ∀ {ρ φ} → TheoryAxiom φ → evalFormula φ ρ
  theorySound (axLogic l) = logicEqSound l
  theorySound (axZFCore z) = zfSound z

  theoryCSound : ∀ {ρ φ} → TheoryCAxiom φ → evalFormula φ ρ
  theoryCSound (axLogicC l) = logicEqSound l
  theoryCSound (axZFCCore zc) = zfcSound zc

  theoryExtSound
    : ∀ {ρ φ}
    → Extensionality
    → TheoryAxiomExt φ
    → evalFormula φ ρ
  theoryExtSound ext (axLogicE l) = logicEqExtSound ext l
  theoryExtSound ext (axZFCoreE z) = zfSound z

  theoryCExtSound
    : ∀ {ρ φ}
    → Extensionality
    → TheoryCAxiomExt φ
    → evalFormula φ ρ
  theoryCExtSound ext (axLogicCE l) = logicEqExtSound ext l
  theoryCExtSound ext (axZFCCoreE zc) = zfcSound zc

  evalAt : Valuation → Formula → Set ℓ
  evalAt ρ φ = evalFormula φ ρ

  -- ------------------------------------------------------------------------
  -- Familiar semantics (Tarski-style) via a probe suite.
  --
  -- Valuations act as probes: each valuation induces a truth-view into
  -- `TruthPreorder`, and the suite refinement is pointwise implication across
  -- all valuations.

  valuationSuite : ProbeSuite Formula Valuation (Sys.TruthPreorder {ℓ})
  valuationSuite = Sys.truthProbeSuite evalAt

  -- Semantic consequence in the fixed model `M`, quantified over all valuations.
  EntailsAll : Formula → Formula → Set ℓ
  EntailsAll Γ φ = Γ ⊑⟦ valuationSuite ⟧ φ

  -- Validity = provability from the empty context (⊤) in the canonical system.
  ValidAll : Formula → Set ℓ
  ValidAll φ = EntailsAll ⊤F φ

  canonicalPresentationAll : Presentation (suiteView valuationSuite)
  canonicalPresentationAll = canonicalSuitePresentation valuationSuite

  completePresentationAll : CompletePresentation canonicalPresentationAll
  completePresentationAll = canonicalSuiteComplete valuationSuite

  canonicalDerivationSystemAll : DerivationSystem (suiteView valuationSuite)
  canonicalDerivationSystemAll =
    canonicalSuiteDerivationSystem valuationSuite ⊤F

  baseSoundAt : ∀ (ρ : Valuation) → evalAt ρ ⊤F
  baseSoundAt ρ x = x

  imp-elimAt
    : (ρ : Valuation)
    → (φ ψ : Formula)
    → evalAt ρ (φ ⇒ ψ)
    → evalAt ρ φ
    → evalAt ρ ψ
  imp-elimAt ρ φ ψ f x = f x

  module EvalAt (ρ : Valuation) where
    presentation
      : Presentation (Sys.truthView (evalAt ρ))
    presentation =
      Sys.presentation {Ax = TheoryAxiom}
        (evalAt ρ)
        (λ {φ} {ψ} → imp-elimAt ρ φ ψ)
        (λ ax → theorySound {ρ} ax)

    derivationSystem
      : DerivationSystem (Sys.truthView (evalAt ρ))
    derivationSystem =
      Sys.derivationSystem {Ax = TheoryAxiom}
        (evalAt ρ)
        (λ {φ} {ψ} → imp-elimAt ρ φ ψ)
        (λ ax → theorySound {ρ} ax)

    canonicalPresentation
      : Presentation (Sys.truthView (evalAt ρ))
    canonicalPresentation = Sys.canonicalPresentation (evalAt ρ)

    canonicalDerivationSystem
      : DerivationSystem (Sys.truthView (evalAt ρ))
    canonicalDerivationSystem = Sys.canonicalDerivationSystem (evalAt ρ)

  presentationAt
    : (ρ : Valuation)
    → Presentation (Sys.truthView (evalAt ρ))
  presentationAt ρ = EvalAt.presentation ρ

  derivationSystemAt
    : (ρ : Valuation)
    → DerivationSystem (Sys.truthView (evalAt ρ))
  derivationSystemAt ρ = EvalAt.derivationSystem ρ

  canonicalPresentationAt
    : (ρ : Valuation)
    → Presentation (Sys.truthView (evalAt ρ))
  canonicalPresentationAt ρ = EvalAt.canonicalPresentation ρ

  canonicalDerivationSystemAt
    : (ρ : Valuation)
    → DerivationSystem (Sys.truthView (evalAt ρ))
  canonicalDerivationSystemAt ρ = EvalAt.canonicalDerivationSystem ρ

  soundDerivation
    : ∀ {ρ Γ φ}
    → Sys.Derives TheoryAxiom Γ φ
    → evalFormula Γ ρ
    → evalFormula φ ρ
  soundDerivation {ρ} =
    Sys.sound {Ax = TheoryAxiom}
      (evalAt ρ)
      (λ {φ} {ψ} → imp-elimAt ρ φ ψ)
      (λ ax → theorySound {ρ} ax)

  soundDerivationAll
    : ∀ {Γ φ}
    → Sys.Derives TheoryAxiom Γ φ
    → EntailsAll Γ φ
  soundDerivationAll d ρ = soundDerivation {ρ = ρ} d

  -- The same Hilbert-style derivability relation can also be packaged as a
  -- presentation behind the *suite* view (pointwise soundness across probes).
  derivesPresentationAll : Presentation (suiteView valuationSuite)
  derivesPresentationAll =
    suitePresentation
      valuationSuite
      (Sys.Derives TheoryAxiom)
      Sys.hyp
      Sys.cut
      soundDerivationAll

  derivesDerivationSystemAll : DerivationSystem (suiteView valuationSuite)
  derivesDerivationSystemAll =
    suiteDerivationSystem
      valuationSuite
      (Sys.Derives TheoryAxiom)
      Sys.hyp
      Sys.cut
      soundDerivationAll
      ⊤F

  -- If the Hilbert relation is complete for the suite semantics, it coincides
  -- with semantic consequence.
  derives↔EntailsAll
    : CompletePresentation derivesPresentationAll
    → ∀ {Γ φ}
    → Sys.Derives TheoryAxiom Γ φ ↔ EntailsAll Γ φ
  derives↔EntailsAll C = presentation↔canonical derivesPresentationAll C

  soundDerivationC
    : ∀ {ρ Γ φ}
    → Sys.Derives TheoryCAxiom Γ φ
    → evalFormula Γ ρ
    → evalFormula φ ρ
  soundDerivationC {ρ} =
    Sys.sound {Ax = TheoryCAxiom}
      (evalAt ρ)
      (λ {φ} {ψ} → imp-elimAt ρ φ ψ)
      (λ ax → theoryCSound {ρ} ax)

  -- Canonical (axiom-free) proofs of the object-language ZF/ZFC axioms:
  -- these are direct semantic consequences in every first-order `Model`.

  zfCanonical : ∀ {ρ φ} → ZFAxiom φ → Sys.CanonicalTheorem (evalAt ρ) φ
  zfCanonical {ρ} ax _ = zfSound {ρ} ax

  zfcCanonical : ∀ {ρ φ} → ZFCAxiom φ → Sys.CanonicalTheorem (evalAt ρ) φ
  zfcCanonical {ρ} ax _ = zfcSound {ρ} ax
