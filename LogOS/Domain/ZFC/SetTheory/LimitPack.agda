{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetTheory.LimitPack where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.ZFC.SetTheory.Pack using (ZFAxioms)

record CumulativeHierarchy {ℓ}
                          {Sig : LogOSSignature ℓ}
                          {Q   : QAdapter ℓ}
                          (K   : Kernel Sig Q)
                          : Set (lsuc (lsuc ℓ)) where
  field
    axioms : ZFAxioms K

  open ZFAxioms axioms public

toZFAxioms
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (CH : CumulativeHierarchy K)
  → ZFAxioms K
toZFAxioms _ CH = CumulativeHierarchy.axioms CH
