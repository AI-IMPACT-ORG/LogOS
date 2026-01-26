{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Assumptions.Separation where

-- Model-theoretic separation, LogOS-style:
-- we separate *meaningful* variants of the domain bundles using explicit
-- nonvacuity / strictness witnesses, rather than relying on meta “no proof
-- exists” claims.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; ⊥)

open import LogOS.Prelude.Ordinal as Ord using (fin)

open import LogOS.API.Assumptions.Core
open import LogOS.Packs.Assumptions.Universality
open import LogOS.Packs.Assumptions.Physics

open import LogOS.Base.Signature using (module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Kernel.LogicKernel using (GTier; LogicKernel)

open import LogOS.Theorems.Meta.Guards using (NontrivialSet)

-- --------------------------------------------------------------------------
-- “Meaningful” wrappers (guards)

record SaturationStrict {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  open LogicCore C renaming (K to LK)
  open LogicKernel LK
  open BulkBoundary BB using (Con_bnd)

  private
    CP∂ : ConPreorder ℓ
    CP∂ = BulkBoundary.bnd BB

    module CP∂ = ConPreorder CP∂

    FlowSat : Con_bnd → Con_bnd
    FlowSat = GTier.Flow G (GTier.sat G)

  field
    c : Con_bnd
    sat≰raw : ¬ (CP∂._⊑_ (FlowSat (Body∂ c)) (Body∂ c))

open SaturationStrict public

record MeaningfulUniversality {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    uni    : UniversalityBundle C
    strict : SaturationStrict C

open MeaningfulUniversality public

record MeaningfulPhysics {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    phys            : PhysicsOfInformationBundle C
    scaleNontrivial : NontrivialSet (QAdapter.Scale (LogicCore.Q C))

open MeaningfulPhysics public

-- --------------------------------------------------------------------------
-- Concrete separation witnesses (in-tree models)

private
  notNontrivial⊤ : ∀ {ℓ : Level} → ¬ NontrivialSet (⊤ {ℓ})
  notNontrivial⊤ (record { a₀ = ttℓ ; a₁ = ttℓ ; a₀≠a₁ = neq }) = neq refl

module Examples where
  -- A computation/irreversibility model with strict saturation at the boundary
  -- (but a trivial cost/energy scale, so physics-of-information is vacuous).
  import LogOS.Domain.UniversalIR.Examples.KernelSaturationLaxTasksNontrivial as U

  coreUni : LogicCore {lzero}
  coreUni = coreFromKernel U.Kℕ

  uniCore : UniversalityBundle coreUni
  uniCore = record { stepGrade = QAdapter.e (LogicCore.Q coreUni) }

  strictUni : SaturationStrict coreUni
  strictUni = record { c = zero ; sat≰raw = λ () }

  meaningfulUni-notPhys
    : MeaningfulUniversality coreUni × ¬ (MeaningfulPhysics coreUni)
  meaningfulUni-notPhys =
    record { uni = uniCore ; strict = strictUni }
    , (λ mp → notNontrivial⊤ (MeaningfulPhysics.scaleNontrivial mp))

  -- A “physics-of-information compatible” core (nontrivial grade/energy carrier),
  -- but with identity Flow (so saturation is not strict: irreversible closure
  -- does not show up at the boundary level).
  import LogOS.Domain.UniversalIR.ObservedKernel as OK
  import LogOS.Domain.Complexity.LCUToLandauer as LCU
  import LogOS.Domain.Complexity.SecondLaw as SL

  module Obs = OK.ForObsKit OK.CodeObsKit

  corePhys : LogicCore {lzero}
  corePhys = coreFromKernel Obs.ObsKernel

  scaleNontrivial-phys : NontrivialSet (QAdapter.Scale (LogicCore.Q corePhys))
  scaleNontrivial-phys =
    record
      { a₀ = fin zero
      ; a₁ = fin (suc zero)
      ; a₀≠a₁ = λ ()
      }

  -- A tiny (toy) Second-Law/Landauer instance on this signature+adapter.
  --
  -- This is deliberately minimal: it only serves as a *model existence witness*
  -- for the “physics” bundle, not as an intended semantics for UniversalIR.

  Obs₂ : Set lzero
  Obs₂ = ⊤ ⊎ ⊤

  o₀ o₁ : Obs₂
  o₀ = inj₁ tt
  o₁ = inj₂ tt

  o₀≠o₁ : ¬ (o₀ ≡ o₁)
  o₀≠o₁ ()

  act-const : Obs.CP.Con → Obs₂ → Obs₂
  act-const _ _ = o₀

  LCUA : LCU.LCUObsAssumptions Obs.Sig Obs.Q
  LCUA =
    record
      { Locality     = ⊤
      ; Causality    = ⊤
      ; Obs          = Obs₂
      ; act          = act-const
      ; LocalUnitary = λ _ → ⊥
      ; unitary-inj  = λ _ ()
      ; L            = QAdapter.e Obs.Q
      ; cost         = λ _ → QAdapter.e Obs.Q
      ; nonUnitary-ref = record { sat-→ = λ _ _ _ → QAdapter.≤s-refl Obs.Q }
      }

  secondLawA : SL.SecondLawAssumptions Obs.Sig Obs.Q
  secondLawA =
    record
      { LCUA = LCUA
      ; Entropy = λ _ → QAdapter.e Obs.Q
      ; unitary-preserves = λ _ ()
      ; nonUnitary→entropy+ = λ _ _ _ → QAdapter.≤s-refl Obs.Q
      }

  secondLawGuardsA : SL.SecondLawGuards Obs.Sig Obs.Q secondLawA
  secondLawGuardsA =
    record
      { mergeWitness =
          LogOSSignature.idC Obs.Sig tt , (o₀ , (o₁ , (o₀≠o₁ , refl)))
      }

  physCore : PhysicsOfInformationBundle corePhys
  physCore =
    record
      { landauer = SL.landauerFromLCU secondLawA
      ; secondLaw = secondLawA
      ; secondLawGuards = secondLawGuardsA
      }

  noStrict-phys : ¬ SaturationStrict corePhys
  noStrict-phys (record { c = c ; sat≰raw = sat≰raw }) =
    let
      open LogicCore corePhys renaming (K to LK)
      open LogicKernel LK
      CP∂ : ConPreorder lzero
      CP∂ = BulkBoundary.bnd BB
      module CP∂ = ConPreorder CP∂
    in
    sat≰raw (CP∂.refl {c = Body∂ c})

  meaningfulPhys-notUni
    : MeaningfulPhysics corePhys × ¬ (MeaningfulUniversality corePhys)
  meaningfulPhys-notUni =
    record { phys = physCore ; scaleNontrivial = scaleNontrivial-phys }
    , (λ mu → noStrict-phys (MeaningfulUniversality.strict mu))
