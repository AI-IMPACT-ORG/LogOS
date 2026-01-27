{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.WeilCriterionDagger where

-- Convenience wrappers: present the Weil/explicit-formula route in a
-- literature-aligned “quadratic positivity” form using a dagger/* structure.
--
-- This does not strengthen any theorem: it is just a lightweight layer that turns a
-- `DaggerTruthPositivity` pack into the existing `TruthPositivity` interface
-- expected by `LogOS.Domain.Opacity.WeilCriterionLedger`.

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)

import LogOS.Theorems.Meta.Dagger as Dag
import LogOS.Domain.Opacity.WeilCriterionLedger as WCL

WeilCriterion†
  : ∀ {ℓT ℓW ℓObs}
    (RS  : RiemannSpectral)
    (DTP : Dag.DaggerTruthPositivity {ℓT} {ℓW} {ℓObs})
  → Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs))
WeilCriterion† RS DTP =
  WCL.WeilCriterion RS (Dag.DaggerTruthPositivity.toTruthPositivity DTP)

WeilCriterionWeak†
  : ∀ {ℓT ℓW ℓObs}
    (RS  : RiemannSpectral)
    (DTP : Dag.DaggerTruthPositivity {ℓT} {ℓW} {ℓObs})
  → Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs))
WeilCriterionWeak† RS DTP =
  WCL.WeilCriterionWeak RS (Dag.DaggerTruthPositivity.toTruthPositivity DTP)

GRH_Without_Vacuity_Guards-from-WeilCriterion†
  : ∀ {ℓT ℓW ℓObs}
    (RS  : RiemannSpectral)
    (DTP : Dag.DaggerTruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterion† RS DTP)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-WeilCriterion† RS DTP WC =
  WCL.GRH_Without_Vacuity_Guards-from-WeilCriterion RS (Dag.DaggerTruthPositivity.toTruthPositivity DTP) WC
