{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.ClosureModel where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Kernel.Endo

open import LogOS.Domain.SetTheory.LimitPack
open import LogOS.Domain.SetTheory.Dsl

open import LogOS.Domain.ZFC.ClosureEndo

-- Experimental scaffold:
-- Given a closure endomap we can *in principle* take its least fixed point (Th⋆)
-- via the tensor/endomap DSL and repackage it as a CumulativeHierarchy / ZFDsl.
-- This module only packages the intended end result as a record interface; it
-- does not claim a completed construction here.

record ClosureHierarchy {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
                        (K : Kernel Sig Q)
                        : Set (lsuc (lsuc ℓ)) where
  field
    closure : ZFCClosure K
    CH      : CumulativeHierarchy K
    surface : ZFDsl K

-- The production set-theory route is WFGraph (`LogOS.Domain.ZFC.WFGraph.*`).
