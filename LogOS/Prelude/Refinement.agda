{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.Refinement where

-- Canonical refinement preorder kit (host-minimal, stdlib-independent).
--
-- Design stance (S/G/H discipline):
-- - use `≡` only for strict/data coherence (S-tier)
-- - use `_⊑_` as the primitive notion of refinement (G-tier)
-- - derive equivalence as mutual refinement (`_≈_`)
--
-- Universe note:
-- The carrier and the refinement relation frequently live in different
-- universes (e.g. function spaces, observational relations on morphisms).
-- So `Refinement` is two-level: (carrier level, relation level).
--
-- Polarity note:
-- Read `c ⊑ d` as “d refines/entails c” (i.e. the right side is stronger).
-- For public-facing surfaces where that polarity is easy to misread, `_≼_`
-- is available below as an order-flavoured presentation alias for the same
-- relation. Reserve plain `≤` for genuinely quantitative orders.

open import LogOS.Host.Level using (Level; lsuc; _⊔_)
open import LogOS.Host.Relation.Binary.PropositionalEquality using (_≡_)
open import LogOS.Host.Product using (_×_; _,_)

record Refinement (ℓCon ℓRel : Level) : Set (lsuc (ℓCon ⊔ ℓRel)) where
  infix 4 _⊑_
  field
    Con   : Set ℓCon
    _⊑_   : Con → Con → Set ℓRel
    refl  : ∀ {c} → c ⊑ c
    trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c

-- Convenience projections (avoid `open Refinement` in downstream modules).
Con : ∀ {ℓCon ℓRel} → Refinement ℓCon ℓRel → Set ℓCon
Con = Refinement.Con

infix 4 _⊑_
_⊑_ : ∀ {ℓCon ℓRel} (CP : Refinement ℓCon ℓRel) → Con CP → Con CP → Set ℓRel
_⊑_ = Refinement._⊑_

infix 4 _≼_
_≼_ : ∀ {ℓCon ℓRel} (CP : Refinement ℓCon ℓRel) → Con CP → Con CP → Set ℓRel
_≼_ = _⊑_

refl⊑ : ∀ {ℓCon ℓRel} (CP : Refinement ℓCon ℓRel) {c : Con CP} → _⊑_ CP c c
refl⊑ CP {c} = Refinement.refl CP

⊑→≼
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
  → _⊑_ CP c d
  → _≼_ CP c d
⊑→≼ le = le

≼→⊑
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
  → _≼_ CP c d
  → _⊑_ CP c d
≼→⊑ le = le

infix 4 _≈_
_≈_ : ∀ {ℓCon ℓRel} (CP : Refinement ℓCon ℓRel) → Con CP → Con CP → Set ℓRel
_≈_ CP x y = (x ⊑[CP] y) × (y ⊑[CP] x)
  where
  infix 4 _⊑[CP]_
  _⊑[CP]_ : Con CP → Con CP → Set _
  _⊑[CP]_ = _⊑_ CP

≈-refl : ∀ {ℓCon ℓRel} (CP : Refinement ℓCon ℓRel) (c : Con CP) → _≈_ CP c c
≈-refl CP c = (refl⊑ CP , refl⊑ CP)

≈-sym
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
  → _≈_ CP c d → _≈_ CP d c
≈-sym (cd , dc) = (dc , cd)

≈→≼-left
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
  → _≈_ CP c d
  → _≼_ CP c d
≈→≼-left (cd , _) = cd

≈→≼-right
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
  → _≈_ CP c d
  → _≼_ CP d c
≈→≼-right (_ , dc) = dc

≡→≈
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {a b : Con CP}
  → a ≡ b → _≈_ CP a b
≡→≈ {CP = CP} eq rewrite eq = (refl⊑ CP , refl⊑ CP)

-- Monotonicity (on endomaps and maps between refinement preorders).

MonoOn
  : ∀ {ℓCon ℓRel} (CP : Refinement ℓCon ℓRel)
  → (Con CP → Con CP)
  → Set (ℓCon ⊔ ℓRel)
MonoOn CP f = ∀ {x y} → x ⊑[CP] y → f x ⊑[CP] f y
  where
  infix 4 _⊑[CP]_
  _⊑[CP]_ : Con CP → Con CP → Set _
  _⊑[CP]_ = _⊑_ CP

MonoMap
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
  → (CP₁ : Refinement ℓCon₁ ℓRel₁) (CP₂ : Refinement ℓCon₂ ℓRel₂)
  → (Con CP₁ → Con CP₂)
  → Set (ℓCon₁ ⊔ ℓRel₁ ⊔ ℓRel₂)
MonoMap CP₁ CP₂ f =
  ∀ {x y} → x ⊑₁ y → f x ⊑₂ f y
  where
  infix 4 _⊑₁_ _⊑₂_
  _⊑₁_ = _⊑_ CP₁
  _⊑₂_ = _⊑_ CP₂

idMonoMap
  : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel}
  → MonoMap CP CP (λ x → x)
idMonoMap le = le

compMonoMap
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂ ℓCon₃ ℓRel₃}
    {CP₁ : Refinement ℓCon₁ ℓRel₁}
    {CP₂ : Refinement ℓCon₂ ℓRel₂}
    {CP₃ : Refinement ℓCon₃ ℓRel₃}
    {f : Con CP₁ → Con CP₂} {g : Con CP₂ → Con CP₃}
  → MonoMap CP₁ CP₂ f → MonoMap CP₂ CP₃ g → MonoMap CP₁ CP₃ (λ x → g (f x))
compMonoMap monoF monoG le = monoG (monoF le)

-- Opposite preorder (reverse refinement direction).
Opp : ∀ {ℓCon ℓRel} → Refinement ℓCon ℓRel → Refinement ℓCon ℓRel
Opp R =
  record
    { Con   = Refinement.Con R
    ; _⊑_   = λ x y → Refinement._⊑_ R y x
    ; refl  = Refinement.refl R
    ; trans = λ xy yz → Refinement.trans R yz xy
    }

-- Product preorder (componentwise refinement).

infixr 30 _×CP_
_×CP_
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂ : Level}
  → Refinement ℓCon₁ ℓRel₁
  → Refinement ℓCon₂ ℓRel₂
  → Refinement (ℓCon₁ ⊔ ℓCon₂) (ℓRel₁ ⊔ ℓRel₂)
_×CP_ R₁ R₂ =
  record
    { Con   = Con R₁ × Con R₂
    ; _⊑_   = λ (x₁ , y₁) (x₂ , y₂) → (x₁ ⊑₁ x₂) × (y₁ ⊑₂ y₂)
    ; refl  = (refl⊑ R₁ , refl⊑ R₂)
    ; trans =
        λ (x₁y₁ , u₁v₁) (y₁z₁ , v₁w₁) →
          ( Refinement.trans R₁ x₁y₁ y₁z₁
          , Refinement.trans R₂ u₁v₁ v₁w₁
          )
    }
  where
    infix 4 _⊑₁_ _⊑₂_
    _⊑₁_ = _⊑_ R₁
    _⊑₂_ = _⊑_ R₂

-- Diagonal map into the product preorder (used for “copying” arguments).
diag
  : ∀ {ℓCon ℓRel : Level} {O : Refinement ℓCon ℓRel}
  → Con O → Con (O ×CP O)
diag x = (x , x)

diag-mono
  : ∀ {ℓCon ℓRel : Level} {O : Refinement ℓCon ℓRel}
  → MonoMap O (O ×CP O) (diag {O = O})
diag-mono le = (le , le)

-- Transport mutual refinement through a monotone map.
monoMap-≈
  : ∀ {ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {CP₁ : Refinement ℓCon₁ ℓRel₁}
    {CP₂ : Refinement ℓCon₂ ℓRel₂}
    {f : Con CP₁ → Con CP₂}
  → MonoMap CP₁ CP₂ f
  → (x y : Con CP₁)
  → _≈_ CP₁ x y
  → _≈_ CP₂ (f x) (f y)
monoMap-≈ monoF _ _ (xy , yx) = (monoF xy , monoF yx)

-- Refinement-first reasoning combinators (chain syntax) for a fixed preorder.
module Reasoning
  {ℓCon ℓRel : Level}
  (CP : Refinement ℓCon ℓRel)
  where

  infix  1 begin⊑_
  infixr 2 _⊑⟨_⟩_
  infix  3 _∎⊑
  infix  1 begin≼_
  infixr 2 _≼⟨_⟩_
  infix  3 _∎≼

  begin⊑_ : ∀ {a b : Con CP} → _⊑_ CP a b → _⊑_ CP a b
  begin⊑_ p = p

  _⊑⟨_⟩_ : ∀ a {b c : Con CP} → _⊑_ CP a b → _⊑_ CP b c → _⊑_ CP a c
  _ ⊑⟨ ab ⟩ bc = Refinement.trans CP ab bc

  _∎⊑ : ∀ a → _⊑_ CP a a
  _∎⊑ a = refl⊑ CP {c = a}

  begin≼_ : ∀ {a b : Con CP} → _≼_ CP a b → _≼_ CP a b
  begin≼_ p = p

  _≼⟨_⟩_ : ∀ a {b c : Con CP} → _≼_ CP a b → _≼_ CP b c → _≼_ CP a c
  _ ≼⟨ ab ⟩ bc = Refinement.trans CP ab bc

  _∎≼ : ∀ a → _≼_ CP a a
  _∎≼ a = refl⊑ CP {c = a}

  infix  1 begin≈_
  infixr 2 _≈⟨_⟩_
  infix  3 _∎≈

  begin≈_ : ∀ {a b : Con CP} → _≈_ CP a b → _≈_ CP a b
  begin≈_ p = p

  _≈⟨_⟩_ : ∀ a {b c : Con CP} → _≈_ CP a b → _≈_ CP b c → _≈_ CP a c
  a ≈⟨ ab ⟩ bc =
    let
      (ab₁ , ba₁) = ab
      (bc₁ , cb₁) = bc
    in
    ( Refinement.trans CP ab₁ bc₁
    , Refinement.trans CP cb₁ ba₁
    )

  _∎≈ : ∀ a → _≈_ CP a a
  _∎≈ a = ≈-refl CP a

-- --------------------------------------------------------------------------
-- Polarity-safe naming helpers.
--
-- Reading reminder: `c ⊑ d` means “d is stronger / entails c”.
-- These synonyms make the intended direction explicit at call sites.
module Polarity where

  Stronger
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel}
    → Con CP → Con CP → Set ℓRel
  Stronger {CP = CP} d c = _⊑_ CP c d

  Entails
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel}
    → Con CP → Con CP → Set ℓRel
  Entails {CP = CP} d c = Stronger {CP = CP} d c

  ⊑→Stronger
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → _⊑_ CP c d
    → Stronger {CP = CP} d c
  ⊑→Stronger le = le

  Stronger→⊑
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → Stronger {CP = CP} d c
    → _⊑_ CP c d
  Stronger→⊑ le = le

  ⊑→Entails
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → _⊑_ CP c d
    → Entails {CP = CP} d c
  ⊑→Entails le = le

  Entails→⊑
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → Entails {CP = CP} d c
    → _⊑_ CP c d
  Entails→⊑ le = le

  ≈→Stronger-left
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → _≈_ CP c d
    → Stronger {CP = CP} d c
  ≈→Stronger-left (cd , _) = cd

  ≈→Stronger-right
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → _≈_ CP c d
    → Stronger {CP = CP} c d
  ≈→Stronger-right (_ , dc) = dc

  ≈→Entails-left
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → _≈_ CP c d
    → Entails {CP = CP} d c
  ≈→Entails-left (cd , _) = cd

  ≈→Entails-right
    : ∀ {ℓCon ℓRel} {CP : Refinement ℓCon ℓRel} {c d : Con CP}
    → _≈_ CP c d
    → Entails {CP = CP} c d
  ≈→Entails-right (_ , dc) = dc

  module StrongerReasoning
    {ℓCon ℓRel : Level}
    (CP : Refinement ℓCon ℓRel)
    where

    infix  1 beginStronger_
    infixr 2 _Stronger⟨_⟩_
    infix  3 _∎Stronger

    beginStronger_
      : ∀ {a b : Con CP}
      → Stronger {CP = CP} a b
      → Stronger {CP = CP} a b
    beginStronger_ p = p

    _Stronger⟨_⟩_
      : ∀ a {b c : Con CP}
      → Stronger {CP = CP} a b
      → Stronger {CP = CP} b c
      → Stronger {CP = CP} a c
    _ Stronger⟨ ab ⟩ bc = Refinement.trans CP bc ab

    _∎Stronger
      : ∀ a
      → Stronger {CP = CP} a a
    _∎Stronger a = refl⊑ CP {c = a}

  module EntailsReasoning
    {ℓCon ℓRel : Level}
    (CP : Refinement ℓCon ℓRel)
    where

    infix  1 beginEntails_
    infixr 2 _Entails⟨_⟩_
    infix  3 _∎Entails

    beginEntails_
      : ∀ {a b : Con CP}
      → Entails {CP = CP} a b
      → Entails {CP = CP} a b
    beginEntails_ p = p

    _Entails⟨_⟩_
      : ∀ a {b c : Con CP}
      → Entails {CP = CP} a b
      → Entails {CP = CP} b c
      → Entails {CP = CP} a c
    _ Entails⟨ ab ⟩ bc = Refinement.trans CP bc ab

    _∎Entails
      : ∀ a
      → Entails {CP = CP} a a
    _∎Entails a = refl⊑ CP {c = a}

  -- Optional: small helper for chained “stronger” reasoning can be added later
  -- in a setting where the intended refinement direction is fixed at call sites.
