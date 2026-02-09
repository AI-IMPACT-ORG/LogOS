{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.EndoRelative where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Closure using (ClosureOp)

open import LogOS.Kernel using (Kernel; module Kernel)
open import LogOS.Kernel.EndoCore public
import LogOS.Kernel.EndoRelativeShared as Shared

module With
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (C   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
  where
  module S = Shared.With (Kernel Sig Q) Kernel.BB
  open S.For K C public

-- Helper: build a relative-closure DSL directly from a `ClosureOp` on the
-- boundary preorder.

module FromClosureOp
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : Kernel Sig Q)
  (C   : ClosureOp (BulkBoundary.bnd (Kernel.BB K)))
  where

  module S = Shared.With (Kernel Sig Q) Kernel.BB
  open S.FromClosureOp K C public
