{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.Types where

open import LogOS.Prelude
open import LogOS.Prelude.List using (List; []; _∷_)

open import LogOS.Apps.ZFC.Proof.Syntax using (Formula)

-- Support information made explicit instead of being collapsed into one list.

record SupportFrame : Set where
  constructor mkSupportFrame
  field
    ambientVars   : List ℕ
    binderVars    : List ℕ
    mandatoryVars : List ℕ

open SupportFrame public

-- Internal formula entries before emission.
--
-- `vars` is the ambient support chosen by the caller before reification. Any
-- binder-introduced support is tracked separately in `SupportFrame`.

record FormulaEntry : Set where
  constructor mkFormulaEntry
  field
    vars    : List ℕ
    formula : Formula

open FormulaEntry public

-- Canonical one-row token row shape.
--
-- `vars` is the normalized mandatory frame used to derive the DB hypotheses for
-- this row.

record TokenEntry : Set where
  constructor mkTokenEntry
  field
    vars : List ℕ
    concl : List ℕ

open TokenEntry public
