{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.SetTheory.FromZFAxioms where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.SetTheory.Pack using (ZFAxioms)
open import LogOS.Domain.SetTheory.LimitPack using (CumulativeHierarchy)

-- `CumulativeHierarchy` and `ZFAxioms` are intentionally field-aligned; this
-- module provides the forward adapter so users can build a staged surface
-- (`StageToCH`) from any existing ZF interpretation pack.

toCumulativeHierarchy
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ZFAxioms K
  → CumulativeHierarchy K
toCumulativeHierarchy _ zf = record { axioms = zf }
