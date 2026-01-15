{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Hom2Cat.Core where

-- Shared (duplication-free) core for the “2-category of kernel morphisms” story:
-- 1-cells: homs + boundary monotonicity
-- 2-cells: pointwise refinement on decoded code maps
-- whiskering + horizontal composition
--
-- Concrete instantiations live in:
-- - `LogOS.Kernel.Hom2Cat`
-- - `LogOS.Kernel.Graded.Hom2Cat`
--
-- The flow-preservation extras are intentionally *not* part of this core, since
-- ungraded and graded kernels use different G-interfaces there.

open import LogOS.Prelude

open import LogOS.Minimal.Con
open import LogOS.Minimal.Con.Rewrite as ConRewrite
open import LogOS.Algebra.ConAlg using (ConAlg ; ConAlgHom≡)

record Kit {ℓ : Level} (Obj : Set (lsuc (lsuc ℓ))) : Set (lsuc (lsuc (lsuc ℓ))) where
  field
    conAlgOf  : Obj → ConAlg {ℓ}

    Code      : Obj → Set ℓ
    decode    : (K : Obj) → Code K → ConPoset.Con (BulkBoundary.bnd (ConAlg.BB (conAlgOf K)))

    Hom       : Obj → Obj → Set (lsuc (lsuc ℓ))
    con-hom   : ∀ {K₁ K₂} → Hom K₁ K₂ → ConAlgHom≡ (conAlgOf K₁) (conAlgOf K₂)
    mapCode   : ∀ {K₁ K₂} → Hom K₁ K₂ → Code K₁ → Code K₂
    map-decode
      : ∀ {K₁ K₂} (h : Hom K₁ K₂) (γ : Code K₁)
      → decode K₂ (mapCode h γ) ≡ ConAlgHom≡.map∂ (con-hom h) (decode K₁ γ)

    idHom     : ∀ K → Hom K K
    composeHom : ∀ {K₁ K₂ K₃} → Hom K₁ K₂ → Hom K₂ K₃ → Hom K₁ K₃

    map∂-id
      : ∀ {K} (c : ConPoset.Con (BulkBoundary.bnd (ConAlg.BB (conAlgOf K))))
      → ConAlgHom≡.map∂ (con-hom (idHom K)) c ≡ c

    map∂-compose
      : ∀ {K₁ K₂ K₃}
        (h₁ : Hom K₁ K₂) (h₂ : Hom K₂ K₃)
        (c : ConPoset.Con (BulkBoundary.bnd (ConAlg.BB (conAlgOf K₁))))
      → ConAlgHom≡.map∂ (con-hom (composeHom h₁ h₂)) c
        ≡ ConAlgHom≡.map∂ (con-hom h₂) (ConAlgHom≡.map∂ (con-hom h₁) c)

    mapCode-id : ∀ {K} (γ : Code K) → mapCode (idHom K) γ ≡ γ
    mapCode-compose
      : ∀ {K₁ K₂ K₃} (h₁ : Hom K₁ K₂) (h₂ : Hom K₂ K₃) (γ : Code K₁)
      → mapCode (composeHom h₁ h₂) γ ≡ mapCode h₂ (mapCode h₁ γ)

open Kit public

module Build {ℓ : Level} {Obj : Set (lsuc (lsuc ℓ))} (K : Kit {ℓ} Obj) where
  open Kit K
    renaming
      ( conAlgOf        to conAlgOfᵏ
      ; Code           to Codeᵏ
      ; decode         to decodeᵏ
      ; Hom            to Homᵏ
      ; con-hom        to con-homᵏ
      ; mapCode        to mapCodeᵏ
      ; map-decode     to map-decodeᵏ
      ; idHom          to idHomᵏ
      ; composeHom     to composeHomᵏ
      ; map∂-id        to map∂-idᵏ
      ; map∂-compose   to map∂-composeᵏ
      ; mapCode-id     to mapCode-idᵏ
      ; mapCode-compose to mapCode-composeᵏ
      )

  CP : Obj → ConPoset ℓ
  CP X = BulkBoundary.bnd (ConAlg.BB (conAlgOfᵏ X))

  map∂
    : ∀ {K₁ K₂} → Homᵏ K₁ K₂
    → ConPoset.Con (CP K₁)
    → ConPoset.Con (CP K₂)
  map∂ h = ConAlgHom≡.map∂ (con-homᵏ h)

  record Hom₁ (K₁ K₂ : Obj) : Set (lsuc (lsuc ℓ)) where
    field
      hom   : Homᵏ K₁ K₂
      mono∂ :
        ∀ {c c'}
        → ConPoset._⊑_ (CP K₁) c c'
        → ConPoset._⊑_ (CP K₂) (map∂ hom c) (map∂ hom c')

    map∂₁ : ConPoset.Con (CP K₁) → ConPoset.Con (CP K₂)
    map∂₁ = map∂ hom

    mapCode₁ : Codeᵏ K₁ → Codeᵏ K₂
    mapCode₁ = mapCodeᵏ hom

    map-decode₁ : ∀ γ → decodeᵏ K₂ (mapCode₁ γ) ≡ map∂₁ (decodeᵏ K₁ γ)
    map-decode₁ γ = map-decodeᵏ hom γ

  open Hom₁ public

  idHom₁ : ∀ (X : Obj) → Hom₁ X X
  idHom₁ X =
    let
      CPX = CP X
      module R = ConRewrite.For CPX
    in
    record
      { hom   = idHomᵏ X
      ; mono∂ = λ {c} {c'} le →
          R.substR (sym (map∂-idᵏ c'))
            (R.substL (sym (map∂-idᵏ c)) le)
      }

  composeHom₁ : ∀ {K₁ K₂ K₃ : Obj} → Hom₁ K₁ K₂ → Hom₁ K₂ K₃ → Hom₁ K₁ K₃
  composeHom₁ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} f g =
    let
      CP₃ = CP K₃
      module R = ConRewrite.For CP₃
      hfg = composeHomᵏ (Hom₁.hom f) (Hom₁.hom g)
    in
    record
      { hom   = hfg
      ; mono∂ = λ {c} {c'} le →
          let
            step₀ = Hom₁.mono∂ f le
            step₁ = Hom₁.mono∂ g step₀
            eqL = map∂-composeᵏ (Hom₁.hom f) (Hom₁.hom g) c
            eqR = map∂-composeᵏ (Hom₁.hom f) (Hom₁.hom g) c'
          in R.substR (sym eqR) (R.substL (sym eqL) step₁)
      }

  infixr 9 _∘₁_
  _∘₁_ : ∀ {K₁ K₂ K₃ : Obj} → Hom₁ K₂ K₃ → Hom₁ K₁ K₂ → Hom₁ K₁ K₃
  g ∘₁ f = composeHom₁ f g

  -- 2-cells: pointwise refinement on decoded code maps at the target object.
  --
  -- Note: this intentionally quotients over code-level distinctions that
  -- decode to the same boundary constraint.

  infix 4 _⇒_
  _⇒_ : ∀ {K₁ K₂ : Obj} → Hom₁ K₁ K₂ → Hom₁ K₁ K₂ → Set ℓ
  _⇒_ {K₂ = K₂} f g =
    ∀ γ →
      ConPoset._⊑_ (CP K₂)
        (decodeᵏ K₂ (Hom₁.mapCode₁ f γ))
        (decodeᵏ K₂ (Hom₁.mapCode₁ g γ))

  -- Named alias to make the quotienting intent explicit in downstream docs.
  RefinesDecode : ∀ {K₁ K₂ : Obj} → Hom₁ K₁ K₂ → Hom₁ K₁ K₂ → Set ℓ
  RefinesDecode = _⇒_

  refl⇒ : ∀ {K₁ K₂ : Obj} (f : Hom₁ K₁ K₂) → f ⇒ f
  refl⇒ {K₂ = K₂} _ γ = ConPoset.refl (CP K₂)

  trans⇒ : ∀ {K₁ K₂ : Obj} {f g h : Hom₁ K₁ K₂} → f ⇒ g → g ⇒ h → f ⇒ h
  trans⇒ {K₂ = K₂} fg gh γ = ConPoset.trans (CP K₂) (fg γ) (gh γ)

  -- Whiskering.

  whiskerR
    : ∀ {K₁ K₂ K₃ : Obj}
      {g g' : Hom₁ K₂ K₃}
      (f : Hom₁ K₁ K₂)
    → g ⇒ g'
    → (g ∘₁ f) ⇒ (g' ∘₁ f)
  whiskerR {K₃ = K₃} {g = g} {g' = g'} f gg' γ =
    let
      CP₃ = CP K₃
      module R = ConRewrite.For CP₃
      eqL : decodeᵏ K₃ (Hom₁.mapCode₁ (g ∘₁ f) γ)
            ≡ decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f γ))
      eqL = cong (decodeᵏ K₃) (mapCode-composeᵏ (Hom₁.hom f) (Hom₁.hom g) γ)
      eqR : decodeᵏ K₃ (Hom₁.mapCode₁ (g' ∘₁ f) γ)
            ≡ decodeᵏ K₃ (Hom₁.mapCode₁ g' (Hom₁.mapCode₁ f γ))
      eqR = cong (decodeᵏ K₃) (mapCode-composeᵏ (Hom₁.hom f) (Hom₁.hom g') γ)
      step : ConPoset._⊑_ CP₃
              (decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f γ)))
              (decodeᵏ K₃ (Hom₁.mapCode₁ g' (Hom₁.mapCode₁ f γ)))
      step = gg' (Hom₁.mapCode₁ f γ)
    in
    R.substR (sym eqR) (R.substL (sym eqL) step)

  whiskerL
    : ∀ {K₁ K₂ K₃ : Obj}
      (g : Hom₁ K₂ K₃)
      {f f' : Hom₁ K₁ K₂}
    → f ⇒ f'
    → (g ∘₁ f) ⇒ (g ∘₁ f')
  whiskerL {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f} {f'} ff' γ =
    let
      CP₃ = CP K₃
      module R = ConRewrite.For CP₃

      eqCompL : decodeᵏ K₃ (Hom₁.mapCode₁ (g ∘₁ f) γ)
                ≡ decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f γ))
      eqCompL = cong (decodeᵏ K₃) (mapCode-composeᵏ (Hom₁.hom f) (Hom₁.hom g) γ)

      eqCompR : decodeᵏ K₃ (Hom₁.mapCode₁ (g ∘₁ f') γ)
                ≡ decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f' γ))
      eqCompR = cong (decodeᵏ K₃) (mapCode-composeᵏ (Hom₁.hom f') (Hom₁.hom g) γ)

      eqL : decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f γ))
            ≡ Hom₁.map∂₁ g (decodeᵏ K₂ (Hom₁.mapCode₁ f γ))
      eqL = map-decodeᵏ (Hom₁.hom g) (Hom₁.mapCode₁ f γ)

      eqR : decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f' γ))
            ≡ Hom₁.map∂₁ g (decodeᵏ K₂ (Hom₁.mapCode₁ f' γ))
      eqR = map-decodeᵏ (Hom₁.hom g) (Hom₁.mapCode₁ f' γ)

      step₀ : ConPoset._⊑_ CP₃
                (Hom₁.map∂₁ g (decodeᵏ K₂ (Hom₁.mapCode₁ f γ)))
                (Hom₁.map∂₁ g (decodeᵏ K₂ (Hom₁.mapCode₁ f' γ)))
      step₀ = Hom₁.mono∂ g (ff' γ)

      step₁ : ConPoset._⊑_ CP₃
                (decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f γ)))
                (Hom₁.map∂₁ g (decodeᵏ K₂ (Hom₁.mapCode₁ f' γ)))
      step₁ = R.substL (sym eqL) step₀

      step₂ : ConPoset._⊑_ CP₃
                (decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f γ)))
                (decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f' γ)))
      step₂ = R.substR (sym eqR) step₁

      step₃ : ConPoset._⊑_ CP₃
                (decodeᵏ K₃ (Hom₁.mapCode₁ (g ∘₁ f) γ))
                (decodeᵏ K₃ (Hom₁.mapCode₁ g (Hom₁.mapCode₁ f' γ)))
      step₃ = R.substL (sym eqCompL) step₂
    in
    R.substR (sym eqCompR) step₃

  -- Naming alignment with Thin2Cat: left/right refers to the varying 1-cell.

  whisker-left
    : ∀ {K₁ K₂ K₃ : Obj}
      {g g' : Hom₁ K₂ K₃}
      (f : Hom₁ K₁ K₂)
    → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f)
  whisker-left {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg' =
    whiskerR {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {g = g} {g' = g'} f gg'

  whisker-right
    : ∀ {K₁ K₂ K₃ : Obj}
      (g : Hom₁ K₂ K₃)
      {f f' : Hom₁ K₁ K₂}
    → f ⇒ f' → (g ∘₁ f) ⇒ (g ∘₁ f')
  whisker-right {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff' =
    whiskerL {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} g {f = f} {f' = f'} ff'

  -- Horizontal composition of 2-cells.

  infixl 7 _⊙_
  _⊙_
    : ∀ {K₁ K₂ K₃ : Obj}
      {f f' : Hom₁ K₁ K₂}
      {g g' : Hom₁ K₂ K₃}
    → f ⇒ f' → g ⇒ g' → (g ∘₁ f) ⇒ (g' ∘₁ f')
  _⊙_ {K₃ = K₃} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg' γ =
    let CP₃ = CP K₃ in
    ConPoset.trans CP₃
      (whiskerR {g = g} {g' = g'} f gg' γ)
      (whiskerL g' {f = f} {f' = f'} ff' γ)

  -- Unit and associativity laws for the thin 2-category.

  id-left⇒
    : ∀ {K₁ K₂ : Obj}
      (f : Hom₁ K₁ K₂)
    → (idHom₁ K₂ ∘₁ f) ⇒ f
  id-left⇒ {K₂ = K₂} f γ =
    let
      CP₂ = CP K₂
      module R = ConRewrite.For CP₂
      eqMap =
        trans
          (mapCode-composeᵏ (Hom₁.hom f) (Hom₁.hom (idHom₁ K₂)) γ)
          (mapCode-idᵏ {K = K₂} (Hom₁.mapCode₁ f γ))
      eqDec = cong (decodeᵏ K₂) eqMap
    in
    R.substR eqDec (ConPoset.refl CP₂)

  id-left⇐
    : ∀ {K₁ K₂ : Obj}
      (f : Hom₁ K₁ K₂)
    → f ⇒ (idHom₁ K₂ ∘₁ f)
  id-left⇐ {K₂ = K₂} f γ =
    let
      CP₂ = CP K₂
      module R = ConRewrite.For CP₂
      eqMap =
        trans
          (mapCode-composeᵏ (Hom₁.hom f) (Hom₁.hom (idHom₁ K₂)) γ)
          (mapCode-idᵏ {K = K₂} (Hom₁.mapCode₁ f γ))
      eqDec = cong (decodeᵏ K₂) eqMap
    in
    R.substR (sym eqDec) (ConPoset.refl CP₂)

  id-right⇒
    : ∀ {K₁ K₂ : Obj}
      (f : Hom₁ K₁ K₂)
    → (f ∘₁ idHom₁ K₁) ⇒ f
  id-right⇒ {K₁ = K₁} {K₂ = K₂} f γ =
    let
      CP₂ = CP K₂
      module R = ConRewrite.For CP₂
      eqMap =
        trans
          (mapCode-composeᵏ (Hom₁.hom (idHom₁ K₁)) (Hom₁.hom f) γ)
          (cong (mapCodeᵏ (Hom₁.hom f)) (mapCode-idᵏ {K = K₁} γ))
      eqDec = cong (decodeᵏ K₂) eqMap
    in
    R.substR eqDec (ConPoset.refl CP₂)

  id-right⇐
    : ∀ {K₁ K₂ : Obj}
      (f : Hom₁ K₁ K₂)
    → f ⇒ (f ∘₁ idHom₁ K₁)
  id-right⇐ {K₁ = K₁} {K₂ = K₂} f γ =
    let
      CP₂ = CP K₂
      module R = ConRewrite.For CP₂
      eqMap =
        trans
          (mapCode-composeᵏ (Hom₁.hom (idHom₁ K₁)) (Hom₁.hom f) γ)
          (cong (mapCodeᵏ (Hom₁.hom f)) (mapCode-idᵏ {K = K₁} γ))
      eqDec = cong (decodeᵏ K₂) eqMap
    in
    R.substR (sym eqDec) (ConPoset.refl CP₂)

  assoc⇒
    : ∀ {K₁ K₂ K₃ K₄ : Obj}
      (f : Hom₁ K₁ K₂)
      (g : Hom₁ K₂ K₃)
      (h : Hom₁ K₃ K₄)
    → ((h ∘₁ g) ∘₁ f) ⇒ (h ∘₁ (g ∘₁ f))
  assoc⇒ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {K₄ = K₄} f g h γ =
    let
      CP₄ = CP K₄
      module R = ConRewrite.For CP₄
      eqL1 =
        mapCode-composeᵏ {K₁ = K₁} {K₂ = K₂} {K₃ = K₄}
          (Hom₁.hom f) (Hom₁.hom (h ∘₁ g)) γ
      eqL2 =
        mapCode-composeᵏ {K₁ = K₂} {K₂ = K₃} {K₃ = K₄}
          (Hom₁.hom g) (Hom₁.hom h) (Hom₁.mapCode₁ f γ)
      eqLeft = trans eqL1 eqL2
      eqR1 =
        mapCode-composeᵏ {K₁ = K₁} {K₂ = K₃} {K₃ = K₄}
          (Hom₁.hom (g ∘₁ f)) (Hom₁.hom h) γ
      eqR2 =
        mapCode-composeᵏ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃}
          (Hom₁.hom f) (Hom₁.hom g) γ
      eqRight =
        trans eqR1
          (cong (mapCodeᵏ (Hom₁.hom h)) eqR2)
      eqMap = trans eqLeft (sym eqRight)
      eqDec = cong (decodeᵏ K₄) eqMap
    in
    R.substR eqDec (ConPoset.refl CP₄)

  assoc⇐
    : ∀ {K₁ K₂ K₃ K₄ : Obj}
      (f : Hom₁ K₁ K₂)
      (g : Hom₁ K₂ K₃)
      (h : Hom₁ K₃ K₄)
    → (h ∘₁ (g ∘₁ f)) ⇒ ((h ∘₁ g) ∘₁ f)
  assoc⇐ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃} {K₄ = K₄} f g h γ =
    let
      CP₄ = CP K₄
      module R = ConRewrite.For CP₄
      eqL1 =
        mapCode-composeᵏ {K₁ = K₁} {K₂ = K₃} {K₃ = K₄}
          (Hom₁.hom (g ∘₁ f)) (Hom₁.hom h) γ
      eqL2 =
        mapCode-composeᵏ {K₁ = K₁} {K₂ = K₂} {K₃ = K₃}
          (Hom₁.hom f) (Hom₁.hom g) γ
      eqLeft =
        trans eqL1
          (cong (mapCodeᵏ (Hom₁.hom h)) eqL2)
      eqR1 =
        mapCode-composeᵏ {K₁ = K₁} {K₂ = K₂} {K₃ = K₄}
          (Hom₁.hom f) (Hom₁.hom (h ∘₁ g)) γ
      eqR2 =
        mapCode-composeᵏ {K₁ = K₂} {K₂ = K₃} {K₃ = K₄}
          (Hom₁.hom g) (Hom₁.hom h) (Hom₁.mapCode₁ f γ)
      eqRight = trans eqR1 eqR2
      eqMap = trans eqLeft (sym eqRight)
      eqDec = cong (decodeᵏ K₄) eqMap
    in
    R.substR eqDec (ConPoset.refl CP₄)

  -- “Homotopy” / observational equivalence: mutual refinement of 2-cells.

  infix 4 _≈_
  _≈_ : ∀ {K₁ K₂ : Obj} → Hom₁ K₁ K₂ → Hom₁ K₁ K₂ → Set ℓ
  f ≈ g = (f ⇒ g) × (g ⇒ f)

  refl≈ : ∀ {K₁ K₂ : Obj} (f : Hom₁ K₁ K₂) → f ≈ f
  refl≈ f = refl⇒ f , refl⇒ f

  sym≈ : ∀ {K₁ K₂ : Obj} {f g : Hom₁ K₁ K₂} → f ≈ g → g ≈ f
  sym≈ (fg , gf) = gf , fg

  trans≈ : ∀ {K₁ K₂ : Obj} {f g h : Hom₁ K₁ K₂} → f ≈ g → g ≈ h → f ≈ h
  trans≈ {f = f} {g = g} {h = h} (fg , gf) (gh , hg) =
    trans⇒ {f = f} {g = g} {h = h} fg gh
    ,
    trans⇒ {f = h} {g = g} {h = f} hg gf

  -- Composition respects ≈ (this is the “Ho-category” congruence law).

  cong-∘₁-≈
    : ∀ {K₁ K₂ K₃ : Obj}
      {f f' : Hom₁ K₁ K₂}
      {g g' : Hom₁ K₂ K₃}
    → f ≈ f'
    → g ≈ g'
    → (g ∘₁ f) ≈ (g' ∘₁ f')
  cong-∘₁-≈ {f = f} {f' = f'} {g = g} {g' = g'} (ff' , f'f) (gg' , g'g) =
    (_⊙_ {f = f} {f' = f'} {g = g} {g' = g'} ff' gg')
    ,
    (_⊙_ {f = f'} {f' = f} {g = g'} {g' = g} f'f g'g)
