{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.ZFC.Signature where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.ObjectLogic.FOL.Syntax as FOL using (Signature)

-- A set-theory-flavoured FOL signature built from a given kernel:
-- - unary predicate symbols are kernel codes (for “coded formulas”)
-- - binary relation symbols are: membership, equality, and coded binary relations.

module ForKernel {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q)
                 where
  open Kernel K

  -- Separate “coded predicates” from “coded relations” at the proof layer.
  -- This prevents accidental arity-mismatch (e.g. using a relation-code where a
  -- predicate-code is expected) while keeping the underlying code type unchanged.

  record ZPredCode : Set ℓ where
    constructor mkPred
    field
      code : Code

  record ZRelCode : Set ℓ where
    constructor mkRel
    field
      code : Code

  open ZPredCode public renaming (code to unPred)
  open ZRelCode  public renaming (code to unRel)

  data ZRel₂ : Set ℓ where
    mem : ZRel₂
    eq  : ZRel₂
    rel : ZRelCode → ZRel₂

  ΣZFC : Signature {ℓ}
  ΣZFC = record
    { PredSym = ZPredCode
    ; RelSym₂ = ZRel₂
    }
