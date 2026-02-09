{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ZFC.SetTheory.FromZFAxioms where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.API.Kernel

open import LogOS.ZFC.SetTheory.Pack using (ZFAxioms)
open import LogOS.ZFC.SetTheory.LimitPack using (CumulativeHierarchy)

-- `CumulativeHierarchy` and `ZFAxioms` are intentionally field-aligned; this
-- module provides the forward adapter so users can build a staged surface
-- (`StageToCH`) from any existing ZF interpretation pack.

toCumulativeHierarchy
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ZFAxioms (kernelLike-fromKernel K)
  → CumulativeHierarchy K
toCumulativeHierarchy _ zf = record { axioms = zf }
