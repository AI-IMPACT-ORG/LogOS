{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Endo where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Closure using (ClosureOp; cl; infl; idemp-lax) renaming (mono to mono-cl)
open import LogOS.Kernel
import LogOS.Kernel.EndoFlowShared as Shared

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where
  FlowClosure
    : (K : Kernel Sig Q)
    → ClosureOp (BulkBoundary.bnd (Kernel.BB K))
  FlowClosure K =
    let open Kernel K in
    record
      { cl        = GTier.Flow G (GTier.sat G)
      ; mono      = GTier.mono G
      ; infl      = GTier.infl-sat G
      ; idemp-lax = GTier.idemp-sat G
      }

  Th*Of
    : (K : Kernel Sig Q)
    → ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K))
  Th*Of K = GTier.Th* (Kernel.G K)

  Th*fixed⇒
    : (K : Kernel Sig Q)
    → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Th*Of K)
        (cl (FlowClosure K) (Th*Of K))
  Th*fixed⇒ K = GTier.Th*-fixed⇒ (Kernel.G K)

  Th*fixed⇐
    : (K : Kernel Sig Q)
    → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (cl (FlowClosure K) (Th*Of K))
        (Th*Of K)
  Th*fixed⇐ K = GTier.Th*-fixed⇐ (Kernel.G K)

  module Flow = Shared.With (Kernel Sig Q) Kernel.BB FlowClosure Th*Of Th*fixed⇒ Th*fixed⇐
  open Flow public
