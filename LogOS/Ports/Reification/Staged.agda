{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Reification.Staged where

-- Stage-indexed admissibility (late-collapse discipline).
--
-- This packages “admissible at stage i” as the primitive interface; ordinary
-- restricted reification is obtained by forgetting stages.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_)
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder)
open import LogOS.LT.Flow using (GuardedClosure; Flow)
open import LogOS.LT.View using (View; μ)

open import LogOS.Ports.Reification.Admissible using
  ( RestrictedReification
  ; TotalReification
  ; total→restricted
  )

unitStageCP : ∀ {ℓCon ℓRel : Level} → ConPreorder ℓCon ℓRel
unitStageCP = UnitPreorder

record StagedReification
  {ℓX ℓCon ℓRel ℓStageCon ℓStageRel ℓR : Level}
  {X : Set ℓX}
  {O : ConPreorder ℓCon ℓRel}
  (obs : View X O)
  : Set (lsuc (ℓX ⊔ ℓCon ⊔ ℓRel ⊔ ℓStageCon ⊔ ℓStageRel ⊔ ℓR)) where
  field
    GC : GuardedClosure O
    stageCP : ConPreorder ℓStageCon ℓStageRel

  Stage : Set ℓStageCon
  Stage = Con stageCP

  infix 4 _≤_
  _≤_ : Stage → Stage → Set ℓStageRel
  _≤_ = _⊑_ stageCP

  field
    ReifiableAt : Stage → Con O → Set ℓR

    monoReifiableAt
      : ∀ {i j} {c : Con O}
      → i ≤ j
      → ReifiableAt i c
      → ReifiableAt j c

    reifyAt : (i : Stage) → (c : Con O) → ReifiableAt i c → X

    decode-reifyAt≈Flow
      : ∀ i c r
      → _≈_ O (μ obs (reifyAt i c r)) (Flow GC c)

open StagedReification public

staged→restricted
  : ∀ {ℓX ℓCon ℓRel ℓStageCon ℓStageRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → StagedReification {ℓStageCon = ℓStageCon} {ℓStageRel = ℓStageRel} {ℓR = ℓR} obs
  → RestrictedReification {ℓR = ℓStageCon ⊔ ℓR} obs
staged→restricted {obs = obs} S =
  record
    { GC = StagedReification.GC S
    ; Reifiable = λ c → Σ (StagedReification.Stage S) (λ i → StagedReification.ReifiableAt S i c)
    ; reify = λ c w → StagedReification.reifyAt S (proj₁ w) c (proj₂ w)
    ; decode-reify≈Flow = λ c w → StagedReification.decode-reifyAt≈Flow S (proj₁ w) c (proj₂ w)
    }

restricted→staged
  : ∀ {ℓX ℓCon ℓRel ℓR ℓStageCon ℓStageRel}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → RestrictedReification {ℓR = ℓR} obs
  → StagedReification {ℓStageCon = ℓStageCon} {ℓStageRel = ℓStageRel} {ℓR = ℓR} obs
restricted→staged {obs = obs} R =
  record
    { GC = RestrictedReification.GC R
    ; stageCP = unitStageCP
    ; ReifiableAt = λ _ c → RestrictedReification.Reifiable R c
    ; monoReifiableAt = λ _ r → r
    ; reifyAt = λ _ c r → RestrictedReification.reify R c r
    ; decode-reifyAt≈Flow = λ _ c r → RestrictedReification.decode-reify≈Flow R c r
    }

staged→total
  : ∀ {ℓX ℓCon ℓRel ℓStageCon ℓStageRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → (S : StagedReification {ℓStageCon = ℓStageCon} {ℓStageRel = ℓStageRel} {ℓR = ℓR} obs)
  → (totalAt : ∀ c → Σ (StagedReification.Stage S) (λ i → StagedReification.ReifiableAt S i c))
  → TotalReification obs
staged→total {obs = obs} S totalAt =
  record
    { GC = StagedReification.GC S
    ; reify = λ c → StagedReification.reifyAt S (proj₁ (totalAt c)) c (proj₂ (totalAt c))
    ; decode-reify≈Flow = λ c → StagedReification.decode-reifyAt≈Flow S (proj₁ (totalAt c)) c (proj₂ (totalAt c))
    }

total→staged
  : ∀ {ℓX ℓCon ℓRel ℓStageCon ℓStageRel ℓR}
    {X : Set ℓX}
    {O : ConPreorder ℓCon ℓRel}
    {obs : View X O}
  → TotalReification obs
  → StagedReification {ℓStageCon = ℓStageCon} {ℓStageRel = ℓStageRel} {ℓR = ℓR} obs
total→staged {obs = obs} T = restricted→staged (total→restricted T)
