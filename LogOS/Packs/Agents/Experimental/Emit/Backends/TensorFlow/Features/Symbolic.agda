{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Symbolic where

open import LogOS.Prelude.List using (List; []; _∷_; _++_)
open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.String using (String; _++s_)

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)
import LogOS.Packs.Agents.Emit.IR.BackendSyntax as BackendSyntax
import LogOS.Packs.Agents.Emit.IR.Intent as Intent

module For (B : Backend) where
  module Py = BackendSyntax.For B

  orBool : Bool → Bool → Bool
  orBool true _ = true
  orBool false b = b

  ifBool : ∀ {A : Set} → Bool → A → A → A
  ifBool true x _ = x
  ifBool false _ y = y

  hasSymbolicConstraints : List Intent.SymbolicConstraint → Bool
  hasSymbolicConstraints [] = false
  hasSymbolicConstraints (_ ∷ _) = true

  hasProofObligations : List String → Bool
  hasProofObligations [] = false
  hasProofObligations (_ ∷ _) = true

  hasSymbolic : Intent.SymbolicIntent → Bool
  hasSymbolic sym =
    orBool
      (hasSymbolicConstraints (Intent.SymbolicIntent.constraints sym))
      (hasProofObligations (Intent.SymbolicIntent.proofObligations sym))

  renderSymbolicConstraint : Intent.SymbolicConstraint → String
  renderSymbolicConstraint (Intent.invariant s) = "invariant: " ++s s
  renderSymbolicConstraint (Intent.rewriteRule s) = "rewrite: " ++s s
  renderSymbolicConstraint (Intent.safetyBarrier s) = "safety: " ++s s
  renderSymbolicConstraint (Intent.typeConstraint s) = "type: " ++s s
  renderSymbolicConstraint (Intent.budgetConstraint s) = "budget: " ++s s

  symbolicConstraintComments : List Intent.SymbolicConstraint → List Py.PyStmt
  symbolicConstraintComments [] = []
  symbolicConstraintComments (c ∷ cs) =
    Py.pyComment (renderSymbolicConstraint c) ∷ symbolicConstraintComments cs

  symbolicProofComments : List String → List Py.PyStmt
  symbolicProofComments [] = []
  symbolicProofComments (p ∷ ps) =
    Py.pyComment ("proof: " ++s p) ∷ symbolicProofComments ps

  symbolicComments : Intent.SymbolicIntent → List Py.PyStmt
  symbolicComments sym =
    ifBool (hasSymbolic sym)
      ( Py.pyComment "symbolic constraints"
        ∷ ( symbolicConstraintComments (Intent.SymbolicIntent.constraints sym)
            ++ symbolicProofComments (Intent.SymbolicIntent.proofObligations sym)
            ++ (Py.pyBlank ∷ []) ) )
      []
