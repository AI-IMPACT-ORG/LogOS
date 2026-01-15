{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Coupling where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; _++s_)

open import LogOS.Packs.Agents.Emit.IR.Backend using (Backend)
import LogOS.Packs.Agents.Emit.IR.BackendSyntax as BackendSyntax
import LogOS.Packs.Agents.Emit.IR.Intent as Intent

module For (B : Backend) where
  module Py = BackendSyntax.For B

  hasCouplingStrategies : List Intent.CouplingStrategy → Bool
  hasCouplingStrategies [] = false
  hasCouplingStrategies (_ ∷ _) = true

  renderScheduleIntent : Intent.ScheduleIntent → String
  renderScheduleIntent Intent.constant = "constant"
  renderScheduleIntent (Intent.linearDecay _ _) = "linearDecay"

  renderCouplingStrategy : Intent.CouplingStrategy → String
  renderCouplingStrategy Intent.guidedDecode = "guided-decode"
  renderCouplingStrategy Intent.lossPenalty = "loss-penalty"
  renderCouplingStrategy Intent.constraintProjection = "constraint-projection"
  renderCouplingStrategy Intent.rejectionSampling = "rejection-sampling"
  renderCouplingStrategy Intent.ruleAugmentedData = "rule-augmented-data"
  renderCouplingStrategy Intent.posteriorRegularization = "posterior-regularization"
  renderCouplingStrategy Intent.proofGuidedSearch = "proof-guided-search"

  couplingStrategyComments : List Intent.CouplingStrategy → List Py.PyStmt
  couplingStrategyComments [] = []
  couplingStrategyComments (s ∷ ss) =
    Py.pyComment ("coupling: " ++s renderCouplingStrategy s)
    ∷ couplingStrategyComments ss

  couplingComments : Intent.CouplingIntent → List Py.PyStmt
  couplingComments coup =
    ifBool (hasCouplingStrategies (Intent.CouplingIntent.strategies coup))
      ( Py.pyComment "hybrid coupling"
        ∷ Py.pyComment
            ("schedule: " ++s renderScheduleIntent (Intent.CouplingIntent.schedule coup))
        ∷ Py.pyComment
            ("strength: " ++s Intent.renderArg (Intent.CouplingIntent.strength coup))
        ∷ ( couplingStrategyComments (Intent.CouplingIntent.strategies coup)
            ++ (Py.pyBlank ∷ []) ) )
      []
    where
      ifBool : ∀ {A : Set} → Bool → A → A → A
      ifBool true x _ = x
      ifBool false _ y = y

  couplingDef : Intent.CouplingIntent → List Py.PyStmt
  couplingDef coup =
    ifBool (hasCouplingStrategies (Intent.CouplingIntent.strategies coup))
      ( Py.pyDef "apply_coupling" ("logits" ∷ "inputs" ∷ "targets" ∷ [])
          ( Py.pyComment "override to inject symbolic coupling"
            ∷ Py.pyReturn (Py.pyVar "logits")
            ∷ [] )
        ∷ Py.pyBlank ∷ [] )
      []
    where
      ifBool : ∀ {A : Set} → Bool → A → A → A
      ifBool true x _ = x
      ifBool false _ y = y

  couplingApplyStmts : Intent.CouplingIntent → String → Py.PyExpr → List Py.PyStmt
  couplingApplyStmts coup inputName lossTarget =
    ifBool (hasCouplingStrategies (Intent.CouplingIntent.strategies coup))
      ( Py.pyAssign "logits"
          (Py.pyCall (Py.pyVar "apply_coupling")
            ( Py.pyPos (Py.pyVar "logits") ∷
              Py.pyPos (Py.pyVar inputName) ∷
              Py.pyPos lossTarget ∷
              [] ))
        ∷ [] )
      []
    where
      ifBool : ∀ {A : Set} → Bool → A → A → A
      ifBool true x _ = x
      ifBool false _ y = y
