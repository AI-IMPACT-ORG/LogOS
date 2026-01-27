{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Capstone where

-- Capstone: CHL as a kernel-native architecture theorem.
-- Bundles proof/model/category/observer views with a single adequacy handle.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Syntax.Prop as Prop using (_↔_)
open import LogOS.Minimal.Con using (MonoOn)

open import LogOS.Kernel hiding (Box; decode-Box; box-mono)

open import LogOS.Kernel.Core as KCore
import LogOS.Theorems.Meta.CHL.Core as Core
import LogOS.Theorems.Meta.CHL.ProofTheory as Proof
import LogOS.Theorems.Meta.CHL.Category as Category
import LogOS.Theorems.Meta.CHL.Completeness as Complete
import LogOS.Theorems.Meta.CHL.SyntaxCompleteness as Syntax

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C  = Core.For K
  module P  = Proof.For K
  module Cat = Category.For K
  module Co  = Complete.For K
  module S   = Syntax.For K

  -- Boundary adequacy witness used for completeness claims.
  Adequacy = Co.BoundaryAdequacy
  ObsAdequacy = Co.BoundaryObsAdequacy
  Budget = Co.Budget

  -- --------------------------------------------------------------------------
  -- Capstone bundle: CHL as a “single theorem with multiple views”.
  -- --------------------------------------------------------------------------

  record Capstone : Set (lsuc (lsuc ℓ)) where
    field
      -- Proof-theory: derivability as refinement from truth.
      prov : P.Prov C.truth

      -- Model-theory: refinement implies boundary entailment.
      sound∂ : ∀ {γ δ} → C.Refines γ δ → Co.Entails∂ γ δ

      -- Category-theory: code/refinement gives an ops-only preorder-category view
      -- (thin/lawful only under an explicit proof-irrelevance assumption); Box is monotone.
      code-cat : Category.ThinCat ℓ
      box-mono : MonoOn (KCore.CodePreorder (Kernel.shape K)) C.Box

      -- Observer view: guarded truth is Flow-stable (for the distinguished code).
      guarded-fixed : C.Refines C.truth (C.Box C.truth)
                    × C.Refines (C.Box C.truth) C.truth

  -- Canonical construction of the capstone bundle.
  capstone : Capstone
  capstone =
    record
      { prov          = P.prov-refl
      ; sound∂        = Co.sound∂
      ; code-cat      = Cat.CodeThinCat
      ; box-mono      = Cat.box-monoOn
      ; guarded-fixed = C.truth-fixed
      }

  -- Full completeness statement (boundary + strict syntax), packaged.
  record CapstoneComplete (A : Adequacy) : Set (lsuc ℓ) where
    field
      boundary-complete
        : ∀ {γ δ} → (C.Refines γ δ) ↔ (Co.Entails∂ γ δ)
      strict-complete
        : ∀ {φ ψ} → (S._⊢S_ φ ψ) ↔ (S.EntailsS φ ψ)

  capstone-complete : ∀ (A : Adequacy) → CapstoneComplete A
  capstone-complete A =
    record
      { boundary-complete = Co.sound-complete∂ A
      ; strict-complete   = S.sound-completeS A
      }

  -- Observational-adequacy variant (same statements, alternative phrasing).
  capstone-complete-obs : ∀ (A : ObsAdequacy) → CapstoneComplete (Co.obs→boundary A)
  capstone-complete-obs A = capstone-complete (Co.obs→boundary A)

  -- Budgeted completeness package (boundary + strict syntax).
  record CapstoneCompleteBudget
    (B : Budget)
    (A : Co.BudgetedAdequacy B)
    : Set (lsuc ℓ) where
    field
      boundary-complete
        : ∀ {γ δ} → (C.Refines γ δ) ↔ (Co.Entails∂-budget B γ δ)
      strict-complete
        : ∀ {φ ψ} → (S._⊢S_ φ ψ) ↔ (S.EntailsS-budget B φ ψ)

  capstone-complete-budget
    : ∀ {B} (A : Co.BudgetedAdequacy B)
    → CapstoneCompleteBudget B A
  capstone-complete-budget A =
    record
      { boundary-complete = Co.sound-complete∂-budget A
      ; strict-complete   = S.sound-completeS-budget A
      }

  -- Hilbert-style packaging (Imp is external, Box is the stable closure modality).
  open P public using (Hilbert; hilbert-from)
