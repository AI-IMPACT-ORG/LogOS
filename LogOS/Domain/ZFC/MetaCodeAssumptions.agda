{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.MetaCodeAssumptions where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

open import LogOS.Domain.SetTheory.Pack as ZFC
import LogOS.Theorems.Meta.Diagonal as Diag
import LogOS.Theorems.Meta.Assumptions.Core as MA

-- ZFC-aligned meta-code assumptions, as a *pack*:
-- these are the ingredients that classical metatheorems (Gödel/Tarski/Rice-style)
-- typically need when internalised in a kernel:
--
-- - a ZF interpretation (`ZFAxioms K`) for ordinary set-level reasoning,
-- - a diagonal/fixed-point schema at the code layer (`Diag.Diagonal K`),
-- - an optional monotone fixed-point principle on boundary constraints (`MA.BoundaryFix K`)
--   for canonical-model style arguments (Knaster–Tarski/Scott shape, up to the preorder).
--
-- This module doesn’t claim derivability of these principles from ZFC inside LogOS;
-- it makes the alignment explicit and keeps the interfaces stable for downstream use.

record ZFCMetaKernel {ℓ}
                    {Sig : LogOSSignature ℓ}
                    {Q   : QAdapter ℓ}
                    (K   : Kernel Sig Q)
                    : Set (lsuc (lsuc ℓ)) where
  field
    zf   : ZFC.ZFAxioms K
    diag : Diag.Diagonal K
    BF   : MA.BoundaryFix K
