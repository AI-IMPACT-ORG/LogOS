{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractLandauer.Core where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)

record CostProfile
  {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (Scale : ConPreorder ℓScaleCon ℓScaleRel)
  (JP : JoinPrequantale Scale)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓScaleCon ⊔ ℓScaleRel)) where
  open Thin2Cat C
  open JoinPrequantale JP
  field
    cost : ∀ {A B} → Con (Hom A B) → Con Scale
    cost-id≈ : ∀ {A} → _≈_ Scale (cost (id {A})) e
    cost-comp⊑
      : ∀ {A B D}
        (f : Con (Hom A B))
        (g : Con (Hom B D))
      → _⊑_ Scale (cost (g ∘ f)) (cost f · cost g)

open CostProfile public

record CostProfileMonotone
  {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Scale : ConPreorder ℓScaleCon ℓScaleRel}
  {JP : JoinPrequantale Scale}
  (L : CostProfile C Scale JP)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓScaleCon ⊔ ℓScaleRel)) where
  open Thin2Cat C
  open CostProfile L
  field
    cost-mono
      : ∀ {A B}
      → MonoMap (Hom A B) Scale (CostProfile.cost L {A = A} {B = B})

open CostProfileMonotone public
