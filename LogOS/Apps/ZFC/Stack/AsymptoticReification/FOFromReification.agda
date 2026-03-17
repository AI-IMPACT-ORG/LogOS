{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.FOFromReification where

open import LogOS.Prelude
open import LogOS.LT.Flow using (Flow)
open import LogOS.LT.ConPreorder using (_⊑_)

import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO
import LogOS.Apps.ZFC.Proof.Syntax as Syn

open import LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort using
  ( PredicateReification
  ; mem-reify-stable↔
  )
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility using
  ( StagedPredicateReification
  ; staged→restricted
  )

-- ------------------------------------------------------------------------
-- FO upgrades from reification (Separation/Replacement as “reify definables”).
--
-- This is where the “approximation” reading becomes concrete:
-- to obtain textbook-style (formula-coded) schemata, it suffices that the
-- reification doctrine makes the relevant FO-definable predicates stable.

module FO {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) (R : PredicateReification (Tower.ZFStackBase.ctx B)) where
  open Tower.ZFStackBase B
  open PredicateReification R
  module FB = TowerFO.ForBase B

  FlowCollapse : Set (lsuc ℓ)
  FlowCollapse = ∀ P → _⊑_ PredBnd (Flow GC P) P

  SepPred : Syn.Formula → FB.Valuation → SetU → Predicate
  SepPred P ρ x z = (z ∈ x) × FB.evalFormula P (FB.extend z (FB.extend x ρ))

  RepPred : Syn.Formula → FB.Valuation → SetU → Predicate
  RepPred R₀ ρ x z =
    Σ SetU (λ u → u ∈ x × FB.evalFormula R₀ (FB.extend u (FB.extend z ρ)))

  record FOWitnesses : Set (lsuc (lsuc ℓ)) where
    field
      sepReifiable
        : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → Reifiable (SepPred P ρ x)

      repReifiable
        : ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → FB.FunctionalOnX R₀ ρ x
        → Reifiable (RepPred R₀ ρ x)

  record FOStability : Set (lsuc (lsuc ℓ)) where
    field
      sepReifiable
        : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → Reifiable (SepPred P ρ x)

      sepStable
        : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → _⊑_ PredBnd (Flow GC (SepPred P ρ x)) (SepPred P ρ x)

      repReifiable
        : ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → FB.FunctionalOnX R₀ ρ x
        → Reifiable (RepPred R₀ ρ x)

      repStable
        : ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → _⊑_ PredBnd (Flow GC (RepPred R₀ ρ x)) (RepPred R₀ ρ x)

  foStabilityFromFlowCollapse
    : FlowCollapse
    → FOWitnesses
    → FOStability
  foStabilityFromFlowCollapse close W =
    record
      { sepReifiable = FOWitnesses.sepReifiable W
      ; sepStable = λ P ρ x → close (SepPred P ρ x)
      ; repReifiable = FOWitnesses.repReifiable W
      ; repStable = λ R₀ ρ x → close (RepPred R₀ ρ x)
      }

  separationFOUpgrade
    : FOStability
    → TowerFO.SeparationFOUpgrade B
  separationFOUpgrade stab =
    record
      { SeparationFV =
          λ P ρ →
            record { μ = λ x → reify (SepPred P ρ x) (FOStability.sepReifiable stab P ρ x) }
      ; separationF-spec =
          λ P ρ x z →
            mem-reify-stable↔
              R
              (SepPred P ρ x)
              (FOStability.sepReifiable stab P ρ x)
              (FOStability.sepStable stab P ρ x)
              z
      }

  replacementFOUpgrade
    : FOStability
    → TowerFO.ReplacementFOUpgrade B
  replacementFOUpgrade stab =
    record
      { ReplacementFV =
          λ R₀ ρ →
            record
              { μ = λ (x , fun) → reify (RepPred R₀ ρ x) (FOStability.repReifiable stab R₀ ρ x fun) }
      ; replacementF-spec =
          λ R₀ ρ x fun z →
            mem-reify-stable↔
              R
              (RepPred R₀ ρ x)
              (FOStability.repReifiable stab R₀ ρ x fun)
              (FOStability.repStable stab R₀ ρ x)
              z
      }

  -- Convenience: package the derived FO upgrades as a `ZFStackFO₋Fnd`.
  zfStackFO₋FndFromReification
    : FOStability
    → TowerFO.ZFStackFO₋Fnd {ℓ}
  zfStackFO₋FndFromReification stab =
    record
      { core =
          TowerFO.mkZFStackFOCore
            B
            (separationFOUpgrade stab)
            (replacementFOUpgrade stab)
      }

  -- Convenience: add a Foundation upgrade, yielding a full `ZFStackFO`.
  zfStackFOFromReification
    : FOStability
    → Tower.FoundationUpgrade B
    → TowerFO.ZFStackFO {ℓ}
  zfStackFOFromReification stab fnd =
    record
      { core =
          TowerFO.mkZFStackFOCore
            B
            (separationFOUpgrade stab)
            (replacementFOUpgrade stab)
      ; fnd = fnd
      }

  -- Convenience: extend the FO stack with a choice upgrade (Foundation not assumed).
  zfcStackFO₋FndFromReification
    : FOStability
    → Tower.ChoiceUpgrade (TowerFO.pairingStackFromBase B)
    → TowerFO.ZFCStackFO₋Fnd {ℓ}
  zfcStackFO₋FndFromReification stab choiceUpg =
    record
      { zf = zfStackFO₋FndFromReification stab
      ; choice = choiceUpg
      }

  -- Convenience: extend the FO stack with Choice + Foundation, yielding `ZFCStackFO`.
  zfcStackFOFromReification
    : FOStability
    → Tower.ChoiceUpgrade (TowerFO.pairingStackFromBase B)
    → Tower.FoundationUpgrade B
    → TowerFO.ZFCStackFO {ℓ}
  zfcStackFOFromReification stab choiceUpg fnd =
    record
      { zf = zfStackFOFromReification stab fnd
      ; choice = choiceUpg
      }

module StagedFO
  {ℓ : Level}
  (B : Tower.ZFStackBase {ℓ})
  (S : StagedPredicateReification (Tower.ZFStackBase.ctx B))
  where

  module R = FO B (staged→restricted S)
  open Tower.ZFStackBase B using (SetU)
  open StagedPredicateReification S
  open R

  record StagedFOWitnesses : Set (lsuc (lsuc ℓ)) where
    field
      sepAt
        : ∀ (P : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → Σ Stage (λ i → ReifiableAt i (SepPred P ρ x))

      repAt
        : ∀ (R₀ : Syn.Formula) (ρ : FB.Valuation) (x : SetU)
        → FB.FunctionalOnX R₀ ρ x
        → Σ Stage (λ i → ReifiableAt i (RepPred R₀ ρ x))

  foWitnesses
    : StagedFOWitnesses
    → FOWitnesses
  foWitnesses W =
    record
      { sepReifiable = λ P ρ x → StagedFOWitnesses.sepAt W P ρ x
      ; repReifiable = λ R₀ ρ x fun → StagedFOWitnesses.repAt W R₀ ρ x fun
      }
