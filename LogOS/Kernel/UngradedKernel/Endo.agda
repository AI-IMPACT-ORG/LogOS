{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax) renaming (mono to mono-cl)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.UngradedKernel
import LogOS.Kernel.EndoFlowShared as Shared

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  FlowClosure
    : (K : UngradedKernel Sig Q)
    → ClosureOp (BulkBoundary.bnd (UngradedKernel.BB K))
  FlowClosure K =
    record
      { cl        = Truth.GuardedCore.GuardedClosure.Flow (UngradedKernel.GTruth K)
      ; mono      = Truth.GuardedCore.GuardedClosure.mono (UngradedKernel.GTruth K)
      ; infl      = Truth.GuardedCore.GuardedClosure.infl (UngradedKernel.GTruth K)
      ; idemp-lax = Truth.GuardedCore.GuardedClosure.idemp-lax (UngradedKernel.GTruth K)
      }

  Th*Of
    : (K : UngradedKernel Sig Q)
    → ConPreorder.Con (BulkBoundary.bnd (UngradedKernel.BB K))
  Th*Of K = Truth.GuardedCore.GuardedClosure.Th* (UngradedKernel.GTruth K)

  Th*fixed⇒
    : (K : UngradedKernel Sig Q)
    → ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K))
        (Th*Of K)
        (cl (FlowClosure K) (Th*Of K))
  Th*fixed⇒ K = Truth.GuardedCore.GuardedClosure.Th*-fixed⇒ (UngradedKernel.GTruth K)

  Th*fixed⇐
    : (K : UngradedKernel Sig Q)
    → ConPreorder._⊑_ (BulkBoundary.bnd (UngradedKernel.BB K))
        (cl (FlowClosure K) (Th*Of K))
        (Th*Of K)
  Th*fixed⇐ K = Truth.GuardedCore.GuardedClosure.Th*-fixed⇐ (UngradedKernel.GTruth K)

  module Flow = Shared.With (UngradedKernel Sig Q) UngradedKernel.BB FlowClosure Th*Of Th*fixed⇒ Th*fixed⇐
  open Flow public
