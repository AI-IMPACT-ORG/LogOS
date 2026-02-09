{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Con.Iso where

-- Order isomorphisms between preorders (up to mutual refinement).

open import LogOS.Prelude

open import LogOS.Minimal.Con using
  ( ConPreorder
  ; PartialOrder
  ; MonoMap
  ; _≈CP_
  ; ≈CP⇒
  ; ≈CP⇐
  ; ≈CP→≡
  )

record PreorderIso {ℓ₁ ℓ₂ : Level}
                   (CP₁ : ConPreorder ℓ₁)
                   (CP₂ : ConPreorder ℓ₂)
                   : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  open ConPreorder CP₁ renaming (Con to Con₁; _⊑_ to _⊑₁_)
  open ConPreorder CP₂ renaming (Con to Con₂; _⊑_ to _⊑₂_)
  field
    to        : Con₁ → Con₂
    from      : Con₂ → Con₁
    to-mono   : MonoMap CP₁ CP₂ to
    from-mono : MonoMap CP₂ CP₁ from
    to∘from≈id : ∀ y → _≈CP_ CP₂ (to (from y)) y
    from∘to≈id : ∀ x → _≈CP_ CP₁ (from (to x)) x

  to-reflects : ∀ {x y} → _⊑₂_ (to x) (to y) → _⊑₁_ x y
  to-reflects {x} {y} toxy =
    let
      x≤fromtox = ≈CP⇐ {CP = CP₁} (from∘to≈id x)
      fromToX≤fromToY = from-mono toxy
      fromToY≤y = ≈CP⇒ {CP = CP₁} (from∘to≈id y)
    in
    ConPreorder.trans CP₁ x≤fromtox (ConPreorder.trans CP₁ fromToX≤fromToY fromToY≤y)

  from-reflects : ∀ {x y} → _⊑₁_ (from x) (from y) → _⊑₂_ x y
  from-reflects {x} {y} fromxy =
    let
      x≤tofromx = ≈CP⇐ {CP = CP₂} (to∘from≈id x)
      tofromx≤tofromy = to-mono fromxy
      tofromy≤y = ≈CP⇒ {CP = CP₂} (to∘from≈id y)
    in
    ConPreorder.trans CP₂ x≤tofromx (ConPreorder.trans CP₂ tofromx≤tofromy tofromy≤y)

open PreorderIso public

module PreorderIsoEq
  {ℓ₁ ℓ₂ : Level}
  {CP₁ : ConPreorder ℓ₁}
  {CP₂ : ConPreorder ℓ₂}
  (po₁ : PartialOrder CP₁)
  (po₂ : PartialOrder CP₂)
  (I : PreorderIso CP₁ CP₂)
  where

  open PreorderIso I renaming
    ( to          to toI
    ; from        to fromI
    ; to∘from≈id  to to∘from≈idI
    ; from∘to≈id  to from∘to≈idI
    )

  to∘from≡id : ∀ y → toI (fromI y) ≡ y
  to∘from≡id y = ≈CP→≡ po₂ (to∘from≈idI y)

  from∘to≡id : ∀ x → fromI (toI x) ≡ x
  from∘to≡id x = ≈CP→≡ po₁ (from∘to≈idI x)
