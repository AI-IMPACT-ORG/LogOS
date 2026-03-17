{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theory.HilbertMP where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Minimal Hilbert system: modus ponens as rule closure.
--
-- Implemented as a special case of the general Metamath-style rule closure
-- transformer `LogOS.LT.Theory.Rules.RuleClosure`.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.LT.ConPreorder using (_⊑_; _≈_)
import LogOS.LT.Theory.Rules as Rules

module HilbertMPLocal
  {ℓ : Level}
  (Formula : Set ℓ)
  (_⇒_ : Formula → Formula → Formula)
  where

  -- A single finitary rule schema for modus ponens:
  -- from (φ ⇒ ψ) and φ, infer ψ.
  data MPRule : Set ℓ where
    mpR : (φ ψ : Formula) → MPRule

  mpSpec : MPRule → Rules.RuleSpec Formula
  mpSpec (mpR φ ψ) =
    record
      { premises = (φ ⇒ ψ) ∷ φ ∷ []
      ; conclusion = ψ
      }

  module RC =
    Rules.RuleClosure
      Formula
      MPRule
      mpSpec

  open Rules.RuleClosure Formula MPRule mpSpec public using
    ( Theory
    ; _⊑T_
    ; TheoryPreorder
    ; hypT
    ; axiomT
    ; theoryClosure
    ; theoryKZ
    ; theoryEffectivity
    ; ClosedTheory
    ; closeTheory
    ; theoryOf
    ; closed-elim
    ; closed-intro
    )
    renaming
      ( DerivesR to DerivesT
      ; mapDerivesR to mapDerivesT
      )

  -- Keep the Hilbert API surface minimal:
  -- expose the closure's proof objects (`DerivesT`) and define the induced
  -- theory transformer (`FlowTheory`) in terms of that proof object layer.
  FlowTheory : (Formula → Set ℓ) → Theory → Theory
  FlowTheory Base T φ = DerivesT Base T φ

  closeTheory-eval⊑FlowTheory
    : ∀ (Base : Formula → Set ℓ) (T : Theory)
    → _⊑_ TheoryPreorder (theoryOf {Base = Base} (closeTheory Base T)) (FlowTheory Base T)
  closeTheory-eval⊑FlowTheory Base T =
    RC.closeTheory-eval⊑FlowTheory Base T

  FlowTheory⊑closeTheory-eval
    : ∀ (Base : Formula → Set ℓ) (T : Theory)
    → _⊑_ TheoryPreorder (FlowTheory Base T) (theoryOf {Base = Base} (closeTheory Base T))
  FlowTheory⊑closeTheory-eval Base T =
    RC.FlowTheory⊑closeTheory-eval Base T

  closeTheory-eval≈FlowTheory
    : ∀ (Base : Formula → Set ℓ) (T : Theory)
    → _≈_ TheoryPreorder (theoryOf {Base = Base} (closeTheory Base T)) (FlowTheory Base T)
  closeTheory-eval≈FlowTheory Base T =
    RC.closeTheory-eval≈FlowTheory Base T

  -- Modus ponens for the specialised rule closure.
  mpT
    : ∀ {Base : Formula → Set ℓ} {T : Theory} {φ ψ : Formula}
    → DerivesT Base T (φ ⇒ ψ)
    → DerivesT Base T φ
    → DerivesT Base T ψ
  mpT {φ = φ} {ψ = ψ} dImp dArg =
    RC.ruleT (mpR φ ψ) (RC.all∷ dImp (RC.all∷ dArg RC.all[]))
