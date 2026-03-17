{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.PartialMaps.Cartesian where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using
  ( ConPreorder
  ; Con
  ; _⊑_
  ; refl⊑
  ; MonoMap
  ; _×CP_
  )
open import LogOS.LT.ConPreorder.Unit using (UnitPreorder)
open import LogOS.Apps.TuringCategory.Lift using
  ( LiftCP
  ; some
  ; bindᴸ
  ; transLiftCP
  ; bindᴸ-mono-l
  ; bindᴸ-mono-r
  )
open import LogOS.Apps.TuringCategory.PartialMaps.Core using (PartialMap; map; mono)

-- --------------------------------------------------------------------------
-- Canonical cartesian structure on `Par` (terminal + binary products).

UnitCP : ∀ {ℓCon ℓRel : Level} → ConPreorder ℓCon ℓRel
UnitCP = UnitPreorder

-- Total morphism into the terminal object.
!
  : ∀ {ℓCon ℓRel : Level} {X : ConPreorder ℓCon ℓRel}
  → PartialMap X (UnitCP {ℓCon} {ℓRel})
! {ℓCon = ℓCon} {ℓRel = ℓRel} {X = X} =
  record
    { map = λ _ → some {CP = UnitCP {ℓCon} {ℓRel}} tt
    ; mono = λ _ → tt
    }

π₁
  : ∀ {ℓCon ℓRel : Level}
    {X Y : ConPreorder ℓCon ℓRel}
  → PartialMap (X ×CP Y) X
π₁ {X = X} {Y = Y} =
  record
    { map = λ xy → some {CP = X} (fst xy)
    ; mono = λ {x} {y} xy≤ → fst xy≤
    }

π₂
  : ∀ {ℓCon ℓRel : Level}
    {X Y : ConPreorder ℓCon ℓRel}
  → PartialMap (X ×CP Y) Y
π₂ {X = X} {Y = Y} =
  record
    { map = λ xy → some {CP = Y} (snd xy)
    ; mono = λ {x} {y} xy≤ → snd xy≤
    }

⟨_,_⟩
  : ∀ {ℓCon ℓRel : Level}
    {Z X Y : ConPreorder ℓCon ℓRel}
  → PartialMap Z X
  → PartialMap Z Y
  → PartialMap Z (X ×CP Y)
⟨_,_⟩ {Z = Z} {X = X} {Y = Y} f g =
  record
    { map = mapPair
    ; mono = monoPair
    }
  where
    mapPair : Con Z → Con (LiftCP (X ×CP Y))
    mapPair z =
      bindᴸ {A = X} {B = X ×CP Y} (map f z) (λ x →
        bindᴸ {A = Y} {B = X ×CP Y} (map g z) (λ y →
          some {CP = X ×CP Y} (x , y)))

    monoPair : MonoMap Z (LiftCP (X ×CP Y)) mapPair
    monoPair {z} {z'} zz' =
      transLiftCP
        {CP = X ×CP Y}
        {a = bindᴸ (map f z) cont}
        {b = bindᴸ (map f z) cont'}
        {c = bindᴸ (map f z') cont'}
        step₁
        step₂
      where
        fzz' : _⊑_ (LiftCP X) (map f z) (map f z')
        fzz' = mono f zz'

        gzz' : _⊑_ (LiftCP Y) (map g z) (map g z')
        gzz' = mono g zz'

        cont : Con X → Con (LiftCP (X ×CP Y))
        cont x =
          bindᴸ {A = Y} {B = X ×CP Y} (map g z) (λ y → some {CP = X ×CP Y} (x , y))

        cont' : Con X → Con (LiftCP (X ×CP Y))
        cont' x =
          bindᴸ {A = Y} {B = X ×CP Y} (map g z') (λ y → some {CP = X ×CP Y} (x , y))

        monoPairY
          : ∀ {x : Con X} {y y' : Con Y}
          → _⊑_ Y y y'
          → _⊑_ (LiftCP (X ×CP Y))
              (some {CP = X ×CP Y} (x , y))
              (some {CP = X ×CP Y} (x , y'))
        monoPairY {x = x} yy' = (refl⊑ X , yy')

        cont≤cont'
          : ∀ x → _⊑_ (LiftCP (X ×CP Y)) (cont x) (cont' x)
        cont≤cont' x =
          bindᴸ-mono-l
            {A = Y}
            {B = X ×CP Y}
            {k = λ y → some {CP = X ×CP Y} (x , y)}
            (λ {y} {y'} yy' → monoPairY {x = x} yy')
            {x = map g z}
            {y = map g z'}
            gzz'

        cont'-mono : MonoMap X (LiftCP (X ×CP Y)) cont'
        cont'-mono {x} {x'} xx' with map g z'
        ... | inj₁ ttℓ = tt
        ... | inj₂ y = (xx' , refl⊑ Y)

        step₁ : _⊑_ (LiftCP (X ×CP Y)) (bindᴸ (map f z) cont) (bindᴸ (map f z) cont')
        step₁ =
          bindᴸ-mono-r
            {A = X}
            {B = X ×CP Y}
            {x = map f z}
            {k = cont}
            {k' = cont'}
            cont≤cont'

        step₂ : _⊑_ (LiftCP (X ×CP Y)) (bindᴸ (map f z) cont') (bindᴸ (map f z') cont')
        step₂ =
          bindᴸ-mono-l
            {A = X}
            {B = X ×CP Y}
            {k = cont'}
            cont'-mono
            {x = map f z}
            {y = map f z'}
            fzz'
