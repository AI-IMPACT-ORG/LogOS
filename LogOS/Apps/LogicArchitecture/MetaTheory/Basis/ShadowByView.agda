{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView where

-- MetaTheory — Observation-induced shadows (pullback refinement on homs).
--
-- v1.1 locality stance:
-- the observation boundary may depend on the object pair `A B` (dependent-first).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _×CP_)
open import LogOS.LT.View using (View; _⊑[_]_; pairView; pairView-fst; pairView-snd)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Shadow using
  ( RefinementShadow
  ; Shadow≤
  )

record ShadowByView
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  (O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂ ⊔ ℓOCon ⊔ ℓORel)) where
  open TwoCellOps C using (Hom₁; Hom₂; _∘1_)
  field
    μ : ∀ {A B} → View (Hom₁ A B) (O A B)

    -- Soundness of the observation: any genuine 2-cell is monotone in `μ`.
    soundμ
      : ∀ {A B} {f g : Hom₁ A B}
      → Hom₂ f g
      → f ⊑[ μ {A} {B} ] g

    -- Compatibility with 1-cell composition (needed for a thin shadow).
    μ-whiskerL
      : ∀ {A B C₀} {f f' : Hom₁ B C₀} {g : Hom₁ A B}
      → f ⊑[ μ {B} {C₀} ] f'
      → (f ∘1 g) ⊑[ μ {A} {C₀} ] (f' ∘1 g)

    μ-whiskerR
      : ∀ {A B C₀} {f : Hom₁ B C₀} {g g' : Hom₁ A B}
      → g ⊑[ μ {A} {B} ] g'
      → (f ∘1 g) ⊑[ μ {A} {C₀} ] (f ∘1 g')

-- Adding probes is product observation (`pairView`) lifted pointwise.
pairShadowByView
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O₁ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₂ ℓORel₂}
  → ShadowByView C O₁
  → ShadowByView C O₂
  → ShadowByView C (λ A B → O₁ A B ×CP O₂ A B)
pairShadowByView {C = C} {O₁ = O₁} {O₂ = O₂} S₁ S₂ =
  let open TwoCellOps C in
  record
    { μ =
        λ {A} {B} →
          pairView (ShadowByView.μ S₁ {A} {B}) (ShadowByView.μ S₂ {A} {B})
    ; soundμ =
        λ {A} {B} {f} {g} α →
          (ShadowByView.soundμ S₁ α , ShadowByView.soundμ S₂ α)
    ; μ-whiskerL =
        λ {A} {B} {C₀} {f} {f'} {g} le →
          ( ShadowByView.μ-whiskerL S₁ (fst le)
          , ShadowByView.μ-whiskerL S₂ (snd le)
          )
    ; μ-whiskerR =
        λ {A} {B} {C₀} {f} {g} {g'} le →
          ( ShadowByView.μ-whiskerR S₁ (fst le)
          , ShadowByView.μ-whiskerR S₂ (snd le)
          )
    }

shadowFromView
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon ℓORel}
  → ShadowByView C O
  → RefinementShadow {ℓRel = ℓORel} C
shadowFromView {C = C} {O = O} S =
  let open TwoCellOps C in
  record
    { _⊑̂_ = λ {A} {B} f g → f ⊑[ ShadowByView.μ S {A} {B} ] g
    ; refl̂ =
        λ {A} {B} {f} →
          ConPreorder.refl (O A B) {c = View.μ (ShadowByView.μ S {A} {B}) f}
    ; tranŝ =
        λ {A} {B} {f} {g} {h} fg gh →
          let
            module R = LogOS.Prelude.RefinementKit.Reasoning (O A B)
          in
          R.begin⊑_
            (R._⊑⟨_⟩_
              (View.μ (ShadowByView.μ S {A} {B}) f)
              fg
              gh)
    ; sound = ShadowByView.soundμ S
    ; whiskerL̂ = ShadowByView.μ-whiskerL S
    ; whiskerR̂ = ShadowByView.μ-whiskerR S
    }

-- Probe accounting: adding probes yields a finer (more discriminating) shadow.
pairShadowByView≤₁
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O₁ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₂ ℓORel₂}
    (S₁ : ShadowByView C O₁)
    (S₂ : ShadowByView C O₂)
  → Shadow≤ (shadowFromView (pairShadowByView S₁ S₂)) (shadowFromView S₁)
pairShadowByView≤₁ {C = C} S₁ S₂ {A} {B} {f} {g} le =
  pairView-fst
    {V₁ = ShadowByView.μ S₁ {A} {B}}
    {V₂ = ShadowByView.μ S₂ {A} {B}}
    {x = f}
    {y = g}
    le

pairShadowByView≤₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O₁ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₂ ℓORel₂}
    (S₁ : ShadowByView C O₁)
    (S₂ : ShadowByView C O₂)
  → Shadow≤ (shadowFromView (pairShadowByView S₁ S₂)) (shadowFromView S₂)
pairShadowByView≤₂ {C = C} S₁ S₂ {A} {B} {f} {g} le =
  pairView-snd
    {V₁ = ShadowByView.μ S₁ {A} {B}}
    {V₂ = ShadowByView.μ S₂ {A} {B}}
    {x = f}
    {y = g}
    le

pairShadowByView-glb
  : ∀ {ℓObj ℓHom₁ ℓHom₂ ℓRel ℓOCon₁ ℓORel₁ ℓOCon₂ ℓORel₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {O₁ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₁ ℓORel₁}
    {O₂ : TwoCellOps.Obj C → TwoCellOps.Obj C → ConPreorder ℓOCon₂ ℓORel₂}
    {S : RefinementShadow {ℓRel = ℓRel} C}
    (S₁ : ShadowByView C O₁)
    (S₂ : ShadowByView C O₂)
  → Shadow≤ S (shadowFromView S₁)
  → Shadow≤ S (shadowFromView S₂)
  → Shadow≤ S (shadowFromView (pairShadowByView S₁ S₂))
pairShadowByView-glb _ _ S≤₁ S≤₂ le = (S≤₁ le , S≤₂ le)
