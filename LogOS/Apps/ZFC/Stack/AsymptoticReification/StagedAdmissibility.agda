{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.AsymptoticReification.StagedAdmissibility where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.View using (View)

import LogOS.Ports.Reification.Admissible as CoreAdmis
import LogOS.Ports.Reification.Staged as CoreStaged

open import LogOS.Apps.ZFC.Stack.Boundary using (PredicateBoundary; membershipView)
import LogOS.Apps.ZFC.Stack.ZFCore as ZF
open import LogOS.Apps.ZFC.Stack.AsymptoticReification.ReificationPort using
  ( PredicateReification
  ; TotalPredicateReification
  ; total→restricted
  ; restricted→total
  )

-- Stage-indexed admissibility as the primitive late-collapse interface.
--
-- This is the LOGᴳ discipline in native form: public reification is staged and
-- admissibility-gated. The ordinary restricted `PredicateReification` surface
-- is derived by forgetting stage indices. A total/unrestricted wrapper can be
-- reconstructed only by supplying an explicit stage-totality witness.
record StagedPredicateReification {ℓ : Level} (C : ZF.SetContext {ℓ})
  : Set (lsuc (lsuc ℓ)) where
  open ZF.SetContext C using (SetU; _∈_; _≈_)

  PredBnd : ConPreorder (lsuc ℓ) ℓ
  PredBnd = PredicateBoundary SetU

  Predicate : Set (lsuc ℓ)
  Predicate = Con PredBnd

  EmptyPred : Predicate
  EmptyPred _ = ⊥

  PairPred : SetU → SetU → Predicate
  PairPred x y z = (z ≈ x) ⊎ (z ≈ y)

  UnionPred : SetU → Predicate
  UnionPred x z = Σ SetU (λ y → (y ∈ x) × (z ∈ y))

  PowersetPred : SetU → Predicate
  PowersetPred x z = ∀ w → w ∈ z → w ∈ x

  field
    GC : GuardedClosure PredBnd
    stageCP : ConPreorder (lsuc ℓ) (lsuc ℓ)

  Stage : Set (lsuc ℓ)
  Stage = Con stageCP

  infix 4 _≤_
  _≤_ : Stage → Stage → Set (lsuc ℓ)
  _≤_ = _⊑_ stageCP

  refl≤ : ∀ {i : Stage} → i ≤ i
  refl≤ = ConPreorder.refl stageCP

  trans≤ : ∀ {i j k : Stage} → i ≤ j → j ≤ k → i ≤ k
  trans≤ {i} ij jk =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning stageCP
    in
    R._⊑⟨_⟩_ i ij jk

  field
    ReifiableAt : Stage → Predicate → Set (lsuc ℓ)

    monoReifiableAt
      : ∀ {i j} {P : Predicate}
      → i ≤ j
      → ReifiableAt i P
      → ReifiableAt j P

    reifyAt
      : (i : Stage)
      → (P : Predicate)
      → ReifiableAt i P
      → SetU

    mem-reifyAt↔
      : ∀ (i : Stage) (P : Predicate) (rP : ReifiableAt i P) (z : SetU)
      → (z ∈ reifyAt i P rP) ↔ (Flow GC P z)

    emptyAt : Σ Stage (λ i → ReifiableAt i EmptyPred)
    pairAt : ∀ x y → Σ Stage (λ i → ReifiableAt i (PairPred x y))
    unionAt : ∀ x → Σ Stage (λ i → ReifiableAt i (UnionPred x))
    powersetAt : ∀ x → Σ Stage (λ i → ReifiableAt i (PowersetPred x))

  obs : View SetU PredBnd
  obs = membershipView SetU _∈_

  core : CoreStaged.StagedReification obs
  core =
    record
      { GC = GC
      ; stageCP = stageCP
      ; ReifiableAt = ReifiableAt
      ; monoReifiableAt = monoReifiableAt
      ; reifyAt = reifyAt
      ; decode-reifyAt≈Flow =
          λ i P rP →
            ( (λ z → _↔_.from (mem-reifyAt↔ i P rP z))
            , (λ z → _↔_.to   (mem-reifyAt↔ i P rP z))
            )
      }

  StagedWitness : Predicate → Set (lsuc ℓ)
  StagedWitness P = Σ Stage (λ i → ReifiableAt i P)

  witnessAt
    : ∀ {i : Stage} {P : Predicate}
    → ReifiableAt i P
    → StagedWitness P
  witnessAt {i = i} rP = i , rP

  weakenAt
    : ∀ {i j : Stage} {P : Predicate}
    → i ≤ j
    → ReifiableAt i P
    → ReifiableAt j P
  weakenAt = monoReifiableAt

  witnessAt≤
    : ∀ {i j : Stage} {P : Predicate}
    → i ≤ j
    → ReifiableAt i P
    → StagedWitness P
  witnessAt≤ {j = j} i≤j rP = j , weakenAt i≤j rP

  restricted : PredicateReification C
  restricted =
    let
      coreR = CoreStaged.staged→restricted core
    in
    record
      { GC = CoreAdmis.RestrictedReification.GC coreR
      ; Reifiable = CoreAdmis.RestrictedReification.Reifiable coreR
      ; reify = CoreAdmis.RestrictedReification.reify coreR
      ; mem-reify↔ =
          λ P w z →
            let
              approx = CoreAdmis.RestrictedReification.decode-reify≈Flow coreR P w
            in
            LogOS.Syntax.Prop.intro (snd approx z) (fst approx z)
      ; emptyReifiable = emptyAt
      ; pairReifiable = pairAt
      ; unionReifiable = unionAt
      ; powersetReifiable = powersetAt
      }

staged→restricted
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → StagedPredicateReification C
  → PredicateReification C
staged→restricted S = StagedPredicateReification.restricted S

restricted→staged
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → PredicateReification C
  → StagedPredicateReification C
restricted→staged R =
  record
    { GC = PredicateReification.GC R
    ; stageCP = CoreStaged.unitStageCP
    ; ReifiableAt = λ _ P → PredicateReification.Reifiable R P
    ; monoReifiableAt = λ _ rP → rP
    ; reifyAt = λ _ P rP → PredicateReification.reify R P rP
    ; mem-reifyAt↔ = λ _ P rP z → PredicateReification.mem-reify↔ R P rP z
    ; emptyAt = tt , PredicateReification.emptyReifiable R
    ; pairAt = λ x y → tt , PredicateReification.pairReifiable R x y
    ; unionAt = λ x → tt , PredicateReification.unionReifiable R x
    ; powersetAt = λ x → tt , PredicateReification.powersetReifiable R x
    }

total→staged
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → TotalPredicateReification C
  → StagedPredicateReification C
total→staged T = restricted→staged (total→restricted T)

staged→total
  : ∀ {ℓ : Level} {C : ZF.SetContext {ℓ}}
  → (S : StagedPredicateReification C)
  → (totalAt : ∀ P → StagedPredicateReification.StagedWitness S P)
  → TotalPredicateReification C
staged→total S = restricted→total (staged→restricted S)
