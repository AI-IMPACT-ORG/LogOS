{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CQM where

-- ============================================================================
-- Categorical Quantum Mechanics (minimal, LogOS-aligned “process theory”)
-- ============================================================================
--
-- The library already has the right primitives to tell a CQM story:
-- - “processes” compose (Scheme/Process DSL)
-- - there is a monoidal structure (kernel tensor, product-like composition)
-- - there is a dagger notion (Meta/Dagger infrastructure)
--
-- This module provides a small *categorical interface* that can be instantiated by:
--   (a) Rel (relations), or
--   (b) a circuit syntax/semantics layer, or
--   (c) a kernel-level endomap DSL.
--
-- Design choice (LogOS-aligned):
-- - morphism equality is pointwise logical equivalence (`↔`) to avoid
--   function extensionality and keep “observational equality” explicit.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_; intro)

open import LogOS.Prelude.Product using (_×_; Σ; _,_)

-- Relations (Set-valued) and observational equality.

Rel : ∀ {ℓA ℓB ℓR : Level} → Set ℓA → Set ℓB → Set (ℓA ⊔ ℓB ⊔ lsuc ℓR)
Rel {ℓR = ℓR} A B = A → B → Set ℓR

infix 3 _≈Rel_
_≈Rel_ : ∀ {ℓA ℓB ℓR} {A : Set ℓA} {B : Set ℓB}
       → Rel {ℓR = ℓR} A B → Rel {ℓR = ℓR} A B → Set (ℓA ⊔ ℓB ⊔ ℓR)
R ≈Rel S = ∀ a b → R a b ↔ S a b

-- A dagger symmetric monoidal category interface (explicit associator/unitors).
-- This is a minimal “CQM core” that can be instantiated by several LogOS layers.

record DaggerSMC
  {ℓO ℓH ℓEq : Level}
  (Obj : Set ℓO)
  : Set (lsuc (ℓO ⊔ ℓH ⊔ ℓEq)) where
  field
    Hom : Obj → Obj → Set ℓH
    _≈_ : ∀ {A B} → Hom A B → Hom A B → Set ℓEq

    id  : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    I    : Obj
    _⊗₀_ : Obj → Obj → Obj
    _⊗₁_ : ∀ {A B C D} → Hom A B → Hom C D → Hom (A ⊗₀ C) (B ⊗₀ D)

    α    : ∀ {A B C} → Hom ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
    α⁻¹  : ∀ {A B C} → Hom (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)

    λL   : ∀ {A} → Hom (I ⊗₀ A) A
    λL⁻¹ : ∀ {A} → Hom A (I ⊗₀ A)

    ρ    : ∀ {A} → Hom (A ⊗₀ I) A
    ρ⁻¹  : ∀ {A} → Hom A (A ⊗₀ I)

    _†   : ∀ {A B} → Hom A B → Hom B A

    -- Category laws (up to ≈)
    assoc : ∀ {A B C D} (h : Hom C D) (g : Hom B C) (f : Hom A B)
          → (h ∘ (g ∘ f)) ≈ ((h ∘ g) ∘ f)
    idl   : ∀ {A B} (f : Hom A B) → (id ∘ f) ≈ f
    idr   : ∀ {A B} (f : Hom A B) → (f ∘ id) ≈ f

    -- Monoidal functoriality
    ⊗-id  : ∀ {A B} → (id {A} ⊗₁ id {B}) ≈ id
    interchange
      : ∀ {A B C D E F} (f₁ : Hom A B) (f₂ : Hom C D)
        (g₁ : Hom B E) (g₂ : Hom D F)
      → ((g₁ ∘ f₁) ⊗₁ (g₂ ∘ f₂)) ≈ ((g₁ ⊗₁ g₂) ∘ (f₁ ⊗₁ f₂))

    -- Coherence isomorphisms (inverse laws)
    α-isoL : ∀ {A B C} → (α {A} {B} {C} ∘ α⁻¹ {A} {B} {C}) ≈ id
    α-isoR : ∀ {A B C} → (α⁻¹ {A} {B} {C} ∘ α {A} {B} {C}) ≈ id
    λ-isoL : ∀ {A} → (λL {A} ∘ λL⁻¹ {A}) ≈ id
    λ-isoR : ∀ {A} → (λL⁻¹ {A} ∘ λL {A}) ≈ id
    ρ-isoL : ∀ {A} → (ρ {A} ∘ ρ⁻¹ {A}) ≈ id
    ρ-isoR : ∀ {A} → (ρ⁻¹ {A} ∘ ρ {A}) ≈ id

    -- Dagger laws
    †-invol : ∀ {A B} (f : Hom A B) → _† (_† f) ≈ f
    †-comp  : ∀ {A B C} (g : Hom B C) (f : Hom A B) → _† (g ∘ f) ≈ ((_† f) ∘ (_† g))
    †-id    : ∀ {A} → _† (id {A}) ≈ id
    †-⊗     : ∀ {A B C D} (f : Hom A B) (g : Hom C D) → _† (f ⊗₁ g) ≈ ((_† f) ⊗₁ (_† g))

  -- Fixities for the mixfix fields (must come after the last field).
  infixr 9 _∘_
  infixl 7 _⊗₀_
  infixl 7 _⊗₁_
  infix  3 _≈_
  infixl 10 _†

open DaggerSMC public

-- Instance: Rel is a dagger SMC with product tensor and converse dagger.
-- This is the standard CQM “Rel model”, and it is lightweight to instantiate.

RelDaggerSMC : ∀ {ℓ} → DaggerSMC {ℓO = lsuc ℓ} {ℓH = lsuc ℓ} {ℓEq = ℓ} (Set ℓ)
RelDaggerSMC {ℓ} =
  let
    Graph : ∀ {A B : Set ℓ} → (A → B) → Rel {ℓR = ℓ} A B
    Graph f a b = b ≡ f a

    assoc× : ∀ {A B C : Set ℓ} → (A × B) × C → A × (B × C)
    assoc× = λ { ((a , b) , c) → (a , (b , c)) }

    unassoc× : ∀ {A B C : Set ℓ} → A × (B × C) → (A × B) × C
    unassoc× = λ { (a , (b , c)) → ((a , b) , c) }

    unitorL : ∀ {A : Set ℓ} → ⊤ × A → A
    unitorL = snd

    unitorL⁻¹ : ∀ {A : Set ℓ} → A → ⊤ × A
    unitorL⁻¹ = λ a → (ttℓ , a)

    unitorR : ∀ {A : Set ℓ} → A × ⊤ → A
    unitorR = fst

    unitorR⁻¹ : ∀ {A : Set ℓ} → A → A × ⊤
    unitorR⁻¹ = λ a → (a , ttℓ)

    assoc-unassoc : ∀ {A B C : Set ℓ} (x : A × (B × C)) → assoc× (unassoc× x) ≡ x
    assoc-unassoc _ = refl

    unassoc-assoc : ∀ {A B C : Set ℓ} (x : (A × B) × C) → unassoc× (assoc× x) ≡ x
    unassoc-assoc _ = refl

    unitorL-iso : ∀ {A : Set ℓ} (a : A) → unitorL (unitorL⁻¹ a) ≡ a
    unitorL-iso _ = refl

    unitorL-iso' : ∀ {A : Set ℓ} (x : ⊤ × A) → unitorL⁻¹ (unitorL x) ≡ x
    unitorL-iso' = λ { (ttℓ , a) → refl }

    unitorR-iso : ∀ {A : Set ℓ} (a : A) → unitorR (unitorR⁻¹ a) ≡ a
    unitorR-iso _ = refl

    unitorR-iso' : ∀ {A : Set ℓ} (x : A × ⊤) → unitorR⁻¹ (unitorR x) ≡ x
    unitorR-iso' = λ { (a , ttℓ) → refl }
  in
  record
    { Hom = λ A B → Rel {ℓR = ℓ} A B
    ; _≈_ = λ {A} {B} R S → R ≈Rel S
    ; id  = λ a b → a ≡ b
    ; _∘_ = λ {A} {B} {C} S R a c → Σ B (λ b → R a b × S b c)

    ; I    = ⊤
    ; _⊗₀_ = _×_
    ; _⊗₁_ = λ {A} {B} {C} {D} R S (a , c) (b , d) → R a b × S c d

    ; α    = Graph assoc×
    ; α⁻¹  = Graph unassoc×
    ; λL   = Graph unitorL
    ; λL⁻¹ = Graph unitorL⁻¹
    ; ρ    = Graph unitorR
    ; ρ⁻¹  = Graph unitorR⁻¹

    ; _† = λ {A} {B} R b a → R a b

    ; assoc = λ {A} {B} {C} {D} h g f a d →
        intro
          (λ { (c , ((b , (fab , gbc)) , hcd)) → (b , (fab , (c , (gbc , hcd)))) })
          (λ { (b , (fab , (c , (gbc , hcd)))) → (c , ((b , (fab , gbc)) , hcd)) })
    ; idl = λ {A} {B} f a b →
        intro
          (λ { (m , (fab , m≡b)) → subst (λ x → f a x) m≡b fab })
          (λ fab → (b , (fab , refl)))
    ; idr = λ {A} {B} f a b →
        intro
          (λ { (m , (a≡m , fmb)) → subst (λ x → f x b) (sym a≡m) fmb })
          (λ fab → (a , (refl , fab)))

    ; ⊗-id = λ {A} {B} (a₁ , b₁) (a₂ , b₂) →
        intro
          (λ { (aa , bb) → cong₂ _,_ aa bb })
          (λ eq → (cong fst eq , cong snd eq))
    ; interchange = λ {A} {B} {C} {D} {E} {F} f₁ f₂ g₁ g₂ (a , c) (e , f) →
        intro
          (λ { ((b , (f₁ab , g₁be)) , (d , (f₂cd , g₂df))) → ((b , d) , ((f₁ab , f₂cd) , (g₁be , g₂df))) })
          (λ { ((b , d) , ((f₁ab , f₂cd) , (g₁be , g₂df))) → ((b , (f₁ab , g₁be)) , (d , (f₂cd , g₂df))) })

    ; α-isoL = λ {A} {B} {C} x y →
        intro
          (λ { (m , (mEq , yEq)) →
                let
                  assocm≡x : assoc× m ≡ x
                  assocm≡x = trans (cong assoc× mEq) (assoc-unassoc x)
                in
                trans (sym assocm≡x) (sym yEq)
            })
          (λ eq → (unassoc× x , (refl , trans (sym eq) (sym (assoc-unassoc x)))))
    ; α-isoR = λ {A} {B} {C} x y →
        intro
          (λ { (m , (mEq , yEq)) →
                let
                  unassocm≡x : unassoc× m ≡ x
                  unassocm≡x = trans (cong unassoc× mEq) (unassoc-assoc x)
                in
                trans (sym unassocm≡x) (sym yEq)
            })
          (λ eq → (assoc× x , (refl , trans (sym eq) (sym (unassoc-assoc x)))))
    ; λ-isoL = λ {A} a a' →
        intro
          (λ { (m , (mEq , eq)) → sym (trans eq (cong unitorL mEq)) })
          (λ eq → (unitorL⁻¹ a , (refl , sym eq)))
    ; λ-isoR = λ {A} x y →
        intro
          (λ { (m , (mEq , eq)) →
                sym (trans (trans eq (cong unitorL⁻¹ mEq)) (unitorL-iso' x))
            })
          (λ eq → (unitorL x , (refl , trans (sym eq) (sym (unitorL-iso' x)))))
    ; ρ-isoL = λ {A} a a' →
        intro
          (λ { (m , (mEq , eq)) → sym (trans eq (cong unitorR mEq)) })
          (λ eq → (unitorR⁻¹ a , (refl , sym eq)))
    ; ρ-isoR = λ {A} x y →
        intro
          (λ { (m , (mEq , eq)) →
                sym (trans (trans eq (cong unitorR⁻¹ mEq)) (unitorR-iso' x))
            })
          (λ eq → (unitorR x , (refl , trans (sym eq) (sym (unitorR-iso' x)))))

    ; †-invol = λ {A} {B} R a b → intro (λ x → x) (λ x → x)
    ; †-comp = λ {A} {B} {C} g f a c →
        intro
          (λ { (b , (fab , gbc)) → (b , (gbc , fab)) })
          (λ { (b , (gbc , fab)) → (b , (fab , gbc)) })
    ; †-id = λ {A} a b → intro sym sym
    ; †-⊗ = λ {A} {B} {C} {D} f g (b , d) (a , c) →
        intro
          (λ { (fba , gdc) → (fba , gdc) })
          (λ { (fba , gdc) → (fba , gdc) })
    }
