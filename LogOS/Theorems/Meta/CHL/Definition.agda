{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Definition where

-- CHL definition pack: propositions/types/programs/proofs are kernel-native.
-- Everything is stated up to refinement/observational equivalence, not equality.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
import LogOS.Minimal.Con.Rewrite as ConRewrite

open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
import LogOS.Theorems.Meta.CHL.Core as Core
import LogOS.Theorems.Meta.CHL.ProofTheory as Proof
import LogOS.Theorems.Meta.CHL.Completeness as Complete
import LogOS.Theorems.Meta.CHL.SyntaxCompleteness as Syntax

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C  = Core.For K
  module P  = Proof.For K
  module Co = Complete.For K
  module S  = Syntax.For K
  private
    CP = BulkBoundary.bnd (Kernel.BB K)
    module R = ConRewrite.For CP

  -- Types and propositions coincide at the code level.
  Type : Set ℓ
  Type = C.Ty

  Prop : Set ℓ
  Prop = Type

  prop≡type : Prop ≡ Type
  prop≡type = refl

  -- Programs/proofs are refinement between codes.
  Program : Type → Type → Set ℓ
  Program = C.Refines

  Proof : Prop → Prop → Set ℓ
  Proof = Program

  -- Terms: proofs from truth.
  Term : Type → Set ℓ
  Term = P.Prov

  truth : Type
  truth = C.truth

  term-truth : Term truth
  term-truth = P.prov-refl

  -- Core rules (identity + cut).
  id : ∀ {A} → Program A A
  id = C.refl-refines

  cut : ∀ {A B C₁} → Program A B → Program B C₁ → Program A C₁
  cut = C.cut-refines

  -- Semantics and modality.
  Sem : Type → ConPreorder.Con CP
  Sem = C.denote

  Box : Type → Type
  Box = C.Box

  box-mono : ∀ {A B} → Program A B → Program (Box A) (Box B)
  box-mono = C.box-mono

  -- Proofs-as-refinement: a literal CHL bridge.
  proofs-as-refinement
    : ∀ {A B}
    → Program A B
      ↔ ConPreorder._⊑_ CP (Sem A) (Sem B)
  proofs-as-refinement = C.proofs-as-refinement

  -- Strict syntax as a view: formulas map into types via encode ∘ TransH.
  Formula : Set ℓ
  Formula = Kernel.Fml K

  FormulaType : Formula → Type
  FormulaType φ = C.encode-code (Kernel.TransH K φ)

  FormulaType-decode : ∀ φ → Sem (FormulaType φ) ≡ Kernel.TransH K φ
  FormulaType-decode φ = C.decode-encode (Kernel.TransH K φ)

  -- Formula derivability (syntax) and its soundness/completeness.
  infix 4 _⊢F_
  _⊢F_ : Formula → Formula → Set ℓ
  _⊢F_ = S._⊢S_

  soundF : ∀ {φ ψ} → φ ⊢F ψ → S.EntailsS φ ψ
  soundF = S.soundS

  completeF
    : Co.BoundaryAdequacy
    → ∀ {φ ψ} → (φ ⊢F ψ) ↔ S.EntailsS φ ψ
  completeF = S.sound-completeS

  completeF-obs
    : Co.BoundaryObsAdequacy
    → ∀ {φ ψ} → (φ ⊢F ψ) ↔ S.EntailsS φ ψ
  completeF-obs = S.sound-completeS-obs

  completeF-budget
    : ∀ {B} → Co.BudgetedAdequacy B
    → ∀ {φ ψ} → (φ ⊢F ψ) ↔ S.EntailsS-budget B φ ψ
  completeF-budget = S.sound-completeS-budget

  -- Bridge between strict derivability and code-level refinement.
  formula-program
    : ∀ {φ ψ}
    → (φ ⊢F ψ)
      ↔ Program (FormulaType φ) (FormulaType ψ)
  formula-program {φ} {ψ} =
    let
      eqL = FormulaType-decode φ
      eqR = FormulaType-decode ψ
    in
    Prop.intro
      (λ le → R.substLR (sym eqL) (sym eqR) le)
      (λ le → R.substLR eqL eqR le)
