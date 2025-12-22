{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Logic.ZFC.Signature where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Logic.FOL.Syntax as FOL using (Signature)

-- A set-theory-flavoured FOL signature built from a given kernel:
-- - unary predicate symbols are kernel codes (for “coded formulas”)
-- - binary relation symbols are: membership, equality, and coded binary relations.

module ForKernel {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q)
                 where
  open Kernel K

  data ZRel₂ : Set ℓ where
    mem : ZRel₂
    eq  : ZRel₂
    rel : Code → ZRel₂

  ΣZFC : Signature {ℓ}
  ΣZFC = record
    { PredSym = Code
    ; RelSym₂ = ZRel₂
    }

