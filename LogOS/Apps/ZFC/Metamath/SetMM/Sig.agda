{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.SetMM.Sig where

open import LogOS.Prelude

-- Token signature for the Set.MM first-order fragment (by symbol index).
record Sig : Set where
  field
    -- Typecode for provable statements (usually "|-").
    tc⊢ : ℕ

    -- Variable typecodes (from `$f` floatings).
    tcWff : ℕ
    tcSet : ℕ

    -- Punctuation / connectives.
    tokLParen tokRParen : ℕ
    tokImp tokAnd tokOr tokIff : ℕ
    tokNot : ℕ
    tokAll tokEx : ℕ
    tokBot : ℕ
    tokEmpty tokOmega : ℕ
    tokUnion tokPower tokSucc : ℕ
    tokPair : ℕ

    -- Atomic relations.
    tokIn tokEq : ℕ

open Sig public

