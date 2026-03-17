{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow where

-- MetaTheory — Thin shadow factorisation (refinement shadows).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _⊑_; ≈-refl)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; idThin2Functor)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps
  ; thinify₂
  )

-- ============================================================================
-- Central theorem (thin shadow factorisation)
-- ============================================================================

record RefinementShadow
  {ℓObj ℓHom₁ ℓHom₂ ℓRel : Level}
  (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓRel)) where
  open TwoCellOps C using (Hom₁; Hom₂; _∘1_)
  infix 4 _⊑̂_
  field
    _⊑̂_ : ∀ {A B} → Hom₁ A B → Hom₁ A B → Set ℓRel
    refl̂ : ∀ {A B} {f : Hom₁ A B} → f ⊑̂ f
    tranŝ
      : ∀ {A B} {f g h : Hom₁ A B}
      → f ⊑̂ g → g ⊑̂ h → f ⊑̂ h

    -- Soundness: genuine 2-cells imply refinement in the chosen shadow.
    sound : ∀ {A B} {f g : Hom₁ A B} → Hom₂ f g → f ⊑̂ g

    whiskerL̂
      : ∀ {A B C} {f f' : Hom₁ B C} {g : Hom₁ A B}
      → f ⊑̂ f' → (f ∘1 g) ⊑̂ (f' ∘1 g)

    whiskerR̂
      : ∀ {A B C} {f : Hom₁ B C} {g g' : Hom₁ A B}
      → g ⊑̂ g' → (f ∘1 g) ⊑̂ (f ∘1 g')

ShadowHomPreorder
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → RefinementShadow {ℓRel = ℓRel} C
  → TwoCellOps.Obj C → TwoCellOps.Obj C
  → ConPreorder ℓHom₁ ℓRel
ShadowHomPreorder {C = C} S A B =
  let open TwoCellOps C in
  record
    { Con = Hom₁ A B
    ; _⊑_ = RefinementShadow._⊑̂_ S
    ; refl = RefinementShadow.refl̂ S
    ; trans = RefinementShadow.tranŝ S
    }

shadowThin2Cat
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → RefinementShadow {ℓRel = ℓRel} C
  → Thin2Cat ℓObj ℓHom₁ ℓRel
shadowThin2Cat {C = C} S =
  record
    { Obj = TwoCellOps.Obj C
    ; Hom = ShadowHomPreorder S
    ; id  = TwoCellOps.id1 C
    ; _∘_ = TwoCellOps._∘1_ C
    ; comp-mono-l = RefinementShadow.whiskerL̂ S
    ; comp-mono-r = RefinementShadow.whiskerR̂ S
    }

-- Canonical (maximally informative) shadow: use the original 2-cells as refinement.
canonicalShadow
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  → RefinementShadow {ℓRel = ℓHom₂} C
canonicalShadow C =
  record
    { _⊑̂_ = TwoCellOps.Hom₂ C
    ; refl̂ = TwoCellOps.id2 C
    ; tranŝ = TwoCellOps._∙2_ C
    ; sound = λ α → α
    ; whiskerL̂ = TwoCellOps.whiskerL2 C
    ; whiskerR̂ = TwoCellOps.whiskerR2 C
    }

canonicalShadow≡thinify₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  → shadowThin2Cat (canonicalShadow C) ≡ thinify₂ C
canonicalShadow≡thinify₂ _ = refl

-- ============================================================================
-- Approximation measures (inclusion order on refinement relations)
-- ============================================================================

Shadow≤
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRelS ℓRelT}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → RefinementShadow {ℓRel = ℓRelS} C
  → RefinementShadow {ℓRel = ℓRelT} C
  → Set (ℓObj ⊔ ℓHom₁ ⊔ ℓRelS ⊔ ℓRelT)
Shadow≤ {C = C} S T =
  ∀ {A B} {f g : TwoCellOps.Hom₁ C A B}
  → RefinementShadow._⊑̂_ S f g
  → RefinementShadow._⊑̂_ T f g

Shadow≤-refl
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {S : RefinementShadow {ℓRel = ℓRel} C}
  → Shadow≤ S S
Shadow≤-refl le = le

Shadow≤-trans
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {S T U : RefinementShadow {ℓRel = ℓRel} C}
  → Shadow≤ S T → Shadow≤ T U → Shadow≤ S U
Shadow≤-trans ST TU le = TU (ST le)

ShadowPreorder
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  → ConPreorder (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓRel)) (ℓObj ⊔ ℓHom₁ ⊔ ℓRel)
ShadowPreorder {ℓRel = ℓRel} C =
  record
    { Con = RefinementShadow {ℓRel = ℓRel} C
    ; _⊑_ = Shadow≤ {C = C}
    ; refl = λ {S} {A} {B} {f} {g} le → le
    ; trans = λ {S} {T} {U} ST TU {A} {B} {f} {g} le → TU (ST le)
    }

-- Any inclusion of shadows (relation implication) induces a canonical thin
-- 2-functor, identity on objects and 1-cells.
shadowWeaken
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRelS ℓRelT}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {S : RefinementShadow {ℓRel = ℓRelS} C}
    {T : RefinementShadow {ℓRel = ℓRelT} C}
  → Shadow≤ S T
  → Thin2Functor (shadowThin2Cat S) (shadowThin2Cat T)
shadowWeaken {T = T} ST =
  let
    D = shadowThin2Cat T
    module D = Thin2Cat D
  in
  record
    { mapObj = λ X → X
    ; mapHom = λ f → f
    ; mapHom-mono = ST
    ; id-pres = λ {A} → ≈-refl (D.Hom A A) _
    ; comp-pres = λ {A} {B} {C₀} f g → ≈-refl (D.Hom A C₀) _
    }

-- Approximation map: any chosen shadow forgets 2-cells into refinement evidence.
shadowApprox
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
  → (S : RefinementShadow {ℓRel = ℓRel} C)
  → Thin2Functor (thinify₂ C) (shadowThin2Cat S)
shadowApprox {C = C} S =
  shadowWeaken {S = canonicalShadow C} {T = S} (RefinementShadow.sound S)

shadowApprox-canonical
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  → shadowApprox (canonicalShadow C) ≡ idThin2Functor (thinify₂ C)
shadowApprox-canonical _ = refl
