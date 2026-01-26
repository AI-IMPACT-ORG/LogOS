{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.WeilCriterionLedger where

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
open import LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack using (GRH_Without_Vacuity_Guards)
open import LogOS.Ports.Semantic.SatMor using (SatRefinement₀; sat-→₀)
open import LogOS.Prelude.Product using (_×_; _,_; fst; snd; proj₁; proj₂)

import LogOS.Theorems.Meta.TruthPositivity as TP
open TP public using (TruthPositivity)
import LogOS.Theorems.Meta.ApplicationKit as AppKit

-- A “Weil criterion / explicit-formula” surface, phrased against an abstract
-- spectral adapter RS and an observer-facing positivity interface TPo.
--
-- The *weak* version is the non-circular core: it does not assume probes are
-- observable, so “zeros off the line” can only be ruled out when the probe is
-- within the observer’s observable/communicable fragment.

record WeilCriterion {ℓT ℓW ℓObs : Level}
                     (RS  : RiemannSpectral)
                     (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
                     : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  open RiemannSpectral RS
  open TP.TruthPositivity TPo
  field
    probe : Spectral → Test
    probe-observable-ref : SatRefinement₀ Spectral
                            (λ _ s → NontrivialZero s)
                            (λ _ s → Observable (probe s))
    probe-pos-ref : SatRefinement₀ Spectral
                     (λ _ s → NontrivialZero s × W-pos (probe s))
                     (λ _ s → OnLine s)

  probe-observable : ∀ s → NontrivialZero s → Observable (probe s)
  probe-observable s nz = sat-→₀ probe-observable-ref s nz

  probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s
  probe-pos→OnLine s nz wp =
    sat-→₀ probe-pos-ref s (nz , wp)

record WeilCriterionWeak {ℓT ℓW ℓObs : Level}
                         (RS  : RiemannSpectral)
                         (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
                         : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
  open RiemannSpectral RS
  open TP.TruthPositivity TPo
  field
    probe : Spectral → Test
    probe-pos-ref : SatRefinement₀ Spectral
                     (λ _ s → NontrivialZero s × W-pos (probe s))
                     (λ _ s → OnLine s)

  probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s
  probe-pos→OnLine s nz wp =
    sat-→₀ probe-pos-ref s (nz , wp)

-- A decomposed (“more manageable”) variant: factor `probe-pos→OnLine` through an
-- intermediate spectral predicate `Mid`. This is useful when the analytic
-- direction is naturally proved in two steps, e.g.:
--   (i) probe-positivity forces a self-duality/symmetry property (`Mid`),
--  (ii) that symmetry property implies the chosen `OnLine` predicate.

record WeilCriterionWeakSplit {ℓT ℓW ℓObs ℓMid : Level}
                              (RS  : RiemannSpectral)
                              (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
                              : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs ⊔ ℓMid)) where
  open RiemannSpectral RS
  open TP.TruthPositivity TPo
  field
    probe : Spectral → Test
    Mid   : Spectral → Set ℓMid
    probe-pos-ref : SatRefinement₀ Spectral
                     (λ _ s → NontrivialZero s × W-pos (probe s))
                     (λ _ s → Mid s)
    Mid→OnLine    : ∀ s → Mid s → OnLine s

  probe-pos→Mid : ∀ s → NontrivialZero s → W-pos (probe s) → Mid s
  probe-pos→Mid s nz wp =
    sat-→₀ probe-pos-ref s (nz , wp)

  probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s
  probe-pos→OnLine s nz wp = Mid→OnLine s (probe-pos→Mid s nz wp)

collapseWeak
  : ∀ {ℓT ℓW ℓObs ℓMid}
    {RS  : RiemannSpectral}
    {TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs}}
  → WeilCriterionWeakSplit {ℓMid = ℓMid} RS TPo
  → WeilCriterionWeak RS TPo
collapseWeak WC = record
  { probe = WeilCriterionWeakSplit.probe WC
  ; probe-pos-ref =
      record
        { sat-→ = λ _ s p →
            WeilCriterionWeakSplit.Mid→OnLine WC s
              (WeilCriterionWeakSplit.probe-pos→Mid WC s (fst p) (snd p))
        }
  }

record WeilCriterionSplit {ℓT ℓW ℓObs ℓMid : Level}
                          (RS  : RiemannSpectral)
                          (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
                          : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs ⊔ ℓMid)) where
  open RiemannSpectral RS
  open TP.TruthPositivity TPo
  field
    probe : Spectral → Test
    probe-observable-ref : SatRefinement₀ Spectral
                            (λ _ s → NontrivialZero s)
                            (λ _ s → Observable (probe s))

    Mid   : Spectral → Set ℓMid
    probe-pos-ref : SatRefinement₀ Spectral
                     (λ _ s → NontrivialZero s × W-pos (probe s))
                     (λ _ s → Mid s)
    Mid→OnLine    : ∀ s → Mid s → OnLine s

  probe-observable : ∀ s → NontrivialZero s → Observable (probe s)
  probe-observable s nz = sat-→₀ probe-observable-ref s nz

  probe-pos→Mid : ∀ s → NontrivialZero s → W-pos (probe s) → Mid s
  probe-pos→Mid s nz wp =
    sat-→₀ probe-pos-ref s (nz , wp)

  probe-pos→OnLine : ∀ s → NontrivialZero s → W-pos (probe s) → OnLine s
  probe-pos→OnLine s nz wp = Mid→OnLine s (probe-pos→Mid s nz wp)

  toWeilCriterion : WeilCriterion RS TPo
  toWeilCriterion = record
    { probe            = probe
    ; probe-observable-ref = probe-observable-ref
    ; probe-pos-ref = record
        { sat-→ = λ _ s p → probe-pos→OnLine s (fst p) (snd p)
        }
    }

  toWeilCriterionWeak : WeilCriterionWeak RS TPo
  toWeilCriterionWeak = collapseWeak (record
    { probe        = probe
    ; Mid          = Mid
    ; probe-pos-ref = probe-pos-ref
    ; Mid→OnLine   = Mid→OnLine
    })

toWeak
  : ∀ {ℓT ℓW ℓObs}
    {RS  : RiemannSpectral}
    {TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs}}
  → WeilCriterion RS TPo → WeilCriterionWeak RS TPo
toWeak WC = record
  { probe = WeilCriterion.probe WC
  ; probe-pos-ref = WeilCriterion.probe-pos-ref WC
  }

-- GRH_Without_Vacuity_Guards “on observable probes”: if a nontrivial zero has an observable probe and
-- the weak criterion holds for that probe, then it lies on the line.

GRH_Without_Vacuity_Guards-on-observable-probes
  : ∀ {ℓT ℓW ℓObs}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterionWeak RS TPo)
  → ∀ s → RiemannSpectral.NontrivialZero RS s
        → TP.TruthPositivity.Observable TPo (WeilCriterionWeak.probe WC s)
        → RiemannSpectral.OnLine RS s
GRH_Without_Vacuity_Guards-on-observable-probes RS TPo WC s nz obs =
  let open TP.TruthPositivity TPo
      open WeilCriterionWeak WC
  in probe-pos→OnLine s nz (positivity (probe s) obs)

-- If you additionally assume observational completeness for the probe family,
-- you recover full GRH_Without_Vacuity_Guards (standard statement).

GRH_Without_Vacuity_Guards-from-weak-criterion+complete
  : ∀ {ℓT ℓW ℓObs}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterionWeak RS TPo)
    (complete-ref : SatRefinement₀ (RiemannSpectral.Spectral RS)
                      (λ _ s → RiemannSpectral.NontrivialZero RS s)
                      (λ _ s → TP.TruthPositivity.Observable TPo (WeilCriterionWeak.probe WC s)))
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-weak-criterion+complete RS TPo WC complete-ref s nz =
  GRH_Without_Vacuity_Guards-on-observable-probes RS TPo WC s nz
    (sat-→₀ complete-ref s nz)

-- One-line form: a full criterion (with probe observability) yields GRH_Without_Vacuity_Guards directly.

GRH_Without_Vacuity_Guards-from-WeilCriterion
  : ∀ {ℓT ℓW ℓObs}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterion RS TPo)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-WeilCriterion RS TPo WC =
  GRH_Without_Vacuity_Guards-from-weak-criterion+complete RS TPo (toWeak WC)
    (WeilCriterion.probe-observable-ref WC)

-- Bridge lemmas: the split forms can be collapsed into the existing criterion
-- records and then discharged by the existing GRH_Without_Vacuity_Guards lemmas.

GRH_Without_Vacuity_Guards-from-weak-split+complete
  : ∀ {ℓT ℓW ℓObs ℓMid}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterionWeakSplit {ℓMid = ℓMid} RS TPo)
    (complete-ref : SatRefinement₀ (RiemannSpectral.Spectral RS)
                      (λ _ s → RiemannSpectral.NontrivialZero RS s)
                      (λ _ s → TP.TruthPositivity.Observable TPo (WeilCriterionWeakSplit.probe WC s)))
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-weak-split+complete RS TPo WC complete-ref =
  GRH_Without_Vacuity_Guards-from-weak-criterion+complete RS TPo (collapseWeak WC) complete-ref

GRH_Without_Vacuity_Guards-from-split
  : ∀ {ℓT ℓW ℓObs ℓMid}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterionSplit {ℓMid = ℓMid} RS TPo)
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-split RS TPo WC =
  GRH_Without_Vacuity_Guards-from-WeilCriterion RS TPo (WeilCriterionSplit.toWeilCriterion WC)

-- Disentangle “observer axiom” from “probe specialisation”:
-- provide a general class of tests that the observer can treat as observable, then
-- show that Weil probes for nontrivial zeros lie in that class.

record ObservableClass {ℓT ℓW ℓObs ℓCls : Level}
                       (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
                       : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs ⊔ ℓCls)) where
  open TP.TruthPositivity TPo
  field
    Class : Test → Set ℓCls
    class→Observable : ∀ {t} → Class t → Observable t

probe-observable-fromClass
  : ∀ {ℓT ℓW ℓObs ℓCls}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterionWeak RS TPo)
    (OC  : ObservableClass {ℓCls = ℓCls} TPo)
    (probe-in-class : ∀ s → RiemannSpectral.NontrivialZero RS s
                        → ObservableClass.Class OC (WeilCriterionWeak.probe WC s))
  → ∀ s → RiemannSpectral.NontrivialZero RS s
        → TP.TruthPositivity.Observable TPo (WeilCriterionWeak.probe WC s)
probe-observable-fromClass RS TPo WC OC probe-in-class s nz =
  ObservableClass.class→Observable OC (probe-in-class s nz)

GRH_Without_Vacuity_Guards-from-weak-criterion+class
  : ∀ {ℓT ℓW ℓObs ℓCls}
    (RS  : RiemannSpectral)
    (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
    (WC  : WeilCriterionWeak RS TPo)
    (OC  : ObservableClass {ℓCls = ℓCls} TPo)
    (probe-in-class : ∀ s → RiemannSpectral.NontrivialZero RS s
                        → ObservableClass.Class OC (WeilCriterionWeak.probe WC s))
  → GRH_Without_Vacuity_Guards RS
GRH_Without_Vacuity_Guards-from-weak-criterion+class RS TPo WC OC probe-in-class =
  GRH_Without_Vacuity_Guards-from-weak-criterion+complete RS TPo WC
    (record
      { sat-→ = λ _ s nz →
          probe-observable-fromClass RS TPo WC OC probe-in-class s nz
      })

-- --------------------------------------------------------------------------
-- Standard pack skeletons (uniform API).
--
-- These wrappers keep the “quartet” entrypoints (`Assumptions`, `Claim`, `Pack`, `mkPack`)
-- scoped, so they can be used operationally without name clashes in the Opacity strand.

module QuartetWeilWeakCriterion {ℓT ℓW ℓObs : Level}
                   (RS  : RiemannSpectral)
                   (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
                   where
  open RiemannSpectral RS
  open TP.TruthPositivity TPo

  record Assumptions : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
    field
      WC       : WeilCriterionWeak RS TPo
      complete-ref : SatRefinement₀ (RiemannSpectral.Spectral RS)
                        (λ _ s → NontrivialZero s)
                        (λ _ s → Observable (WeilCriterionWeak.probe WC s))

    complete : ∀ s → NontrivialZero s → Observable (WeilCriterionWeak.probe WC s)
    complete s nz = sat-→₀ complete-ref s nz

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (λ A →
        GRH_Without_Vacuity_Guards-from-weak-criterion+complete RS TPo
          (Assumptions.WC A)
          (Assumptions.complete-ref A))
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)

module QuartetWeilCriterion {ℓT ℓW ℓObs : Level}
               (RS  : RiemannSpectral)
               (TPo : TP.TruthPositivity {ℓT} {ℓW} {ℓObs})
               where
  record Assumptions : Set (lsuc (ℓT ⊔ ℓW ⊔ ℓObs)) where
    field
      WC : WeilCriterion RS TPo

  Claim : Assumptions → Set
  Claim _ = GRH_Without_Vacuity_Guards RS

  module Q =
    AppKit.MakeDerived Assumptions Claim
      (λ A → GRH_Without_Vacuity_Guards-from-WeilCriterion RS TPo (Assumptions.WC A))
  open Q public using (Pack; assumptionsOf; claimOf; mkPack)
