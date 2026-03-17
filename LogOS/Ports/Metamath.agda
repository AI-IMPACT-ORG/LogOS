{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Metamath where

-- A Metamath-style “database port” in LogOS shape.
--
-- - a set of labels (assertions),
-- - each label carries a finite list of hypotheses and a conclusion.
--
-- Closing a ledger under such assertions is a guarded-closure transformer on
-- theories; see `LogOS.LT.Theory.Rules`.

open import LogOS.Prelude
open import LogOS.Prelude.List using (List)

open import LogOS.LT.Flow using (GuardedClosure)
open import LogOS.LT.Effectivity using (Effectivity)
import LogOS.LT.Theory.Rules as Rules

record Database {ℓ : Level} (Formula : Set ℓ) : Set (lsuc ℓ) where
  field
    Label  : Set ℓ
    hyps   : Label → List Formula
    concl  : Label → Formula

open Database public
module FromDB
  {ℓ : Level}
  {Formula : Set ℓ}
  (DB : Database Formula)
  where

  open Database DB renaming (Label to LabelOf; hyps to hypsOf; concl to conclOf)

  ruleSpec : LabelOf → Rules.RuleSpec Formula
  ruleSpec l =
    record
      { premises = hypsOf l
      ; conclusion = conclOf l
      }

  module MM =
    Rules.RuleClosure
      Formula
      LabelOf
      ruleSpec

  open MM public
  -- Convenience alias: the Metamath closure transformer for this database.
  mmClosure : (Base : Formula → Set ℓ) → GuardedClosure TheoryPreorder
  mmClosure = theoryClosure

  mmEffectivity
    : (Base : Formula → Set ℓ)
    → Effectivity TheoryPreorder
  mmEffectivity = theoryEffectivity
