{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.EndoRelative where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Closure using (ClosureOp)

open import LogOS.Kernel.UngradedKernel using (UngradedKernel; module UngradedKernel)
open import LogOS.Kernel.UngradedKernel.EndoCore public
import LogOS.Kernel.EndoRelativeShared as Shared

module With
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : UngradedKernel Sig Q)
  (C   : ClosureOp (BulkBoundary.bnd (UngradedKernel.BB K)))
  where
  module S = Shared.With (UngradedKernel Sig Q) UngradedKernel.BB
  open S.For K C public

module FromClosureOp
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (K   : UngradedKernel Sig Q)
  (C   : ClosureOp (BulkBoundary.bnd (UngradedKernel.BB K)))
  where

  module S = Shared.With (UngradedKernel Sig Q) UngradedKernel.BB
  open S.FromClosureOp K C public
