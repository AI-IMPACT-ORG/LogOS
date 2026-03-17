{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.AbstractDeutschToPar where

-- Bridge: view the Deutsch-style category `LOGᴰ` (a port stack over physical semantics)
-- inside the canonical partial-map model `Par`, by functorial forgetting:
--
--   LOGᴰ  --forgetDeutschLOG-->  LOG  --codeToPar-->  Par
--
-- This is intentionally structural: it does not identify “physical states” with
-- partial-map domains. The object mapping is the induced **code preorder**
-- (`CodePreorder`), aligned with how `LOG` compares morphisms (decoded behaviour).
--
-- Optional lift:
-- given an explicit CH2008 indexing ledger on `Par` (`ParTuringLedger`), we can
-- further lift into tracked partial maps (`ParTracked U TU`) via `deutschToParTracked`.

open import LogOS.Prelude
open import LogOS.LT.Thin2Functor using (Thin2Functor; _∘F_)

import LogOS.Apps.TuringCategory.Bridge.KernelToPar as K2Par
import LogOS.Apps.TuringCategory.PartialMaps as PM
import LogOS.Apps.TuringCategory.ParTracked as Tracked
import LogOS.Apps.TuringCategory.ParTuring as ParT

import LogOS.Ports.PhysicalSemantics.Core as Phys
import LogOS.Ports.AbstractDeutsch2Cat as Deutsch

deutschToPar
  : ∀ {ℓI ℓOCon ℓORel ℓCode : Level}
  → (PS : Phys.DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  → Thin2Functor
      (Deutsch.Deutsch2CatLocal.Deutsch.WithPort {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS)
      (PM.Par {ℓCon = ℓCode} {ℓRel = ℓI ⊔ ℓORel})
deutschToPar {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS =
  let
    module D = Deutsch.Deutsch2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS
    module Loc = D.Locality
    module Cau = D.Causality
    module DeutschPort = D.Deutsch
  in
  K2Par.codeToPar {ℓ = ℓI ⊔ ℓOCon} {ℓRel = ℓI ⊔ ℓORel} {ℓCode = ℓCode}
    ∘F
  (Loc.forgetPhysical ∘F (Cau.forget ∘F DeutschPort.forget))

-- Optional lift through “tracked” partial maps (Grothendieck/Σ-totalisation;
-- refinement inherited from the base; displayed evidence ignored):
-- given an explicit indexing ledger on `Par`, we can decorate the `Par`-image
-- of every Deutsch morphism with its chosen tracker.
deutschToParTracked
  : ∀ {ℓI ℓOCon ℓORel ℓCode : Level}
  → (PS : Phys.DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  → (L : ParT.ParTuringLedger {ℓCon = ℓCode} {ℓRel = ℓI ⊔ ℓORel})
  → Thin2Functor
      (Deutsch.Deutsch2CatLocal.Deutsch.WithPort {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS)
      (Tracked.ParTracked (ParT.U L) (ParT.TU L))
deutschToParTracked {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS L =
  Tracked.trackPar (ParT.U L) (ParT.TU L)
    ∘F
  deutschToPar {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS
