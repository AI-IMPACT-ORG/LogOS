{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.ObservableSector where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Theorems.Meta.TruthPositivity as TP
import LogOS.Domain.Opacity.WeilCriterionLedger as WCL

-- Observable sector / superselection story for GRH_Without_Vacuity_Guards (quantum-aligned reading):
--
-- The weak Weil criterion only gives:
--   (NontrivialZero s) ∧ (Observable (probe s))  ⇒  OnLine s
--
-- Therefore, any off-line nontrivial zero must lie outside the observer’s
-- observable fragment (its probe is non-observable). If you *choose* an
-- “observable test algebra” (ObservableClass) and assume all Weil probes land in it,
-- GRH_Without_Vacuity_Guards follows. Otherwise, off-line zeros are forced into a superselection sector:
-- they cannot couple to the chosen observable class of tests.

module For {ℓT ℓW ℓObs : Level}
           (RS  : RiemannSpectral)
           (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
           (WC  : WCL.WeilCriterionWeak RS TPo)
           where

  open RiemannSpectral RS
  open TP.TruthPositivity TPo

  probe : Spectral → Test
  probe = WCL.WeilCriterionWeak.probe WC

  -- Non-observable sector: nontrivial zeros whose Weil probe is outside Observable.
  HiddenZero : Spectral → Set (lzero ⊔ ℓObs)
  HiddenZero s = NontrivialZero s × ¬ Observable (probe s)

  offLine→¬ObservableProbe
    : ∀ s → NontrivialZero s → ¬ OnLine s → ¬ Observable (probe s)
  offLine→¬ObservableProbe s nz notOnLine obs =
    notOnLine (WCL.GRH_Without_Vacuity_Guards-on-observable-probes RS TPo WC s nz obs)

  offLine→HiddenZero : ∀ s → NontrivialZero s → ¬ OnLine s → HiddenZero s
  offLine→HiddenZero s nz notOnLine =
    nz , offLine→¬ObservableProbe s nz notOnLine

  -- Relative to a chosen “observable test algebra” (ObservableClass), off-line zeros
  -- must lie outside it (otherwise they would become observable and hence OnLine).
  offLine→probeOutsideClass
    : ∀ {ℓCls}
      (OC : WCL.ObservableClass {ℓCls = ℓCls} TPo)
      → ∀ s → NontrivialZero s → ¬ OnLine s
      → ¬ WCL.ObservableClass.Class OC (probe s)
  offLine→probeOutsideClass OC s nz notOnLine inClass =
    offLine→¬ObservableProbe s nz notOnLine
      (WCL.ObservableClass.class→Observable OC inClass)

  -- If the chosen observable class contains all Weil probes (a scoped “choice /
  -- observational completeness” axiom), then GRH_Without_Vacuity_Guards holds.
  GRH_Without_Vacuity_Guards-from-observableClass
    : ∀ {ℓCls}
      (OC : WCL.ObservableClass {ℓCls = ℓCls} TPo)
      → (probe-in-class : ∀ s → NontrivialZero s → WCL.ObservableClass.Class OC (probe s))
      → GRH_Without_Vacuity_Guards RS
  GRH_Without_Vacuity_Guards-from-observableClass OC probe-in-class =
    WCL.GRH_Without_Vacuity_Guards-from-weak-criterion+class RS TPo WC OC probe-in-class
