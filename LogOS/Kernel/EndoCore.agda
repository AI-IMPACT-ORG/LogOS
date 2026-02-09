{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.EndoCore where

-- Boundary endomaps and pointwise refinements for a given `Kernel` K.
-- This is the base layer shared by:
-- - the Flow-specialised DSL in `Kernel.Endo`, and
-- - the modality-relative DSL in `Kernel.EndoRelative`.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
import LogOS.Minimal.Thin2Cat as Thin2Cat
import LogOS.Minimal.RelPreorder as RP
import LogOS.Minimal.RelThin2Cat as RelThin2Cat
open import LogOS.Kernel

infix 4 _≤₂_
infix 4 _≈₂_
infixr 9 _∘E_

record Endo {ℓ : Level}
            {Sig : LogOSSignature ℓ}
            {Q   : QAdapter ℓ}
            (K   : Kernel Sig Q)
            : Set (lsuc ℓ) where
  open Kernel K
  private
    Con∂ = ConPreorder.Con (BulkBoundary.bnd BB)
    _≤_  = ConPreorder._⊑_ (BulkBoundary.bnd BB)
  field
    fn   : Con∂ → Con∂
    mono : ∀ {x y} → x ≤ y → fn x ≤ fn y

open Endo public

-- Pointwise refinement between endomaps.
_≤₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : Kernel Sig Q) → Endo K → Endo K → Set ℓ
_≤₂_ {ℓ} {Sig} {Q} K f g = ∀ c →
  let open Kernel K in
  ConPreorder._⊑_ (BulkBoundary.bnd BB) (Endo.fn f c) (Endo.fn g c)

-- Mutual refinement between endomaps (pointwise, in the boundary preorder).
_≈₂_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       (K : Kernel Sig Q) → Endo K → Endo K → Set ℓ
_≈₂_ K f g = (_≤₂_ K f g) × (_≤₂_ K g f)

-- Identity and composition on endomaps.

idEndo : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) → Endo K
idEndo K .Endo.fn   = λ c → c
idEndo K .Endo.mono = λ p → p

_∘E_ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       {K : Kernel Sig Q} → Endo K → Endo K → Endo K
_∘E_ {K = K} f g .Endo.fn   = λ c → Endo.fn f (Endo.fn g c)
_∘E_ {K = K} f g .Endo.mono = λ p → Endo.mono f (Endo.mono g p)

-- Refinement basics.

refl₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
        (K : Kernel Sig Q) (f : Endo K) → _≤₂_ K f f
refl₂ K f = λ _ →
  let open Kernel K in
  ConPreorder.refl (BulkBoundary.bnd BB)

trans₂ : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q)
         {f g h : Endo K} → _≤₂_ K f g → _≤₂_ K g h → _≤₂_ K f h
trans₂ K fg gh = λ c →
  let open Kernel K in
  ConPreorder.trans (BulkBoundary.bnd BB) (fg c) (gh c)

≈₂-refl
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q) (f : Endo K) → _≈₂_ K f f
≈₂-refl K f = (refl₂ K f , refl₂ K f)

≈₂-sym
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q} {f g : Endo K}
  → _≈₂_ K f g → _≈₂_ K g f
≈₂-sym (fg , gf) = (gf , fg)

≈₂-trans
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    {f g h : Endo K}
  → _≈₂_ K f g → _≈₂_ K g h → _≈₂_ K f h
≈₂-trans K {f} {g} {h} (fg , gf) (gh , hg) =
  ( trans₂ K {f = f} {g = g} {h = h} fg gh
  , trans₂ K {f = h} {g = g} {h = f} hg gf
  )

-- Endomaps form a one-object locally preordered 2-category; whiskering is inherited.

EndoPreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → ConPreorder (lsuc ℓ)
EndoPreorder {ℓ} K =
  record
    { Con = Endo K
    ; _⊑_ = λ f g → Lift (lsuc ℓ) (_≤₂_ K f g)
    ; refl = λ {f} → lift (refl₂ K f)
    ; trans = λ {f} {g} {h} fg gh →
        lift (trans₂ K {f = f} {g = g} {h = h} (Lift.lower fg) (Lift.lower gh))
    }

EndoThin2Cat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Thin2Cat.Thin2Cat ℓ (lsuc ℓ)
EndoThin2Cat K =
  record
    { Obj = ⊤
    ; Hom = λ _ _ → EndoPreorder K
    ; id  = λ {A} → idEndo K
    ; _∘_ = _∘E_
    ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} fg →
        lift (λ c → Lift.lower fg (Endo.fn g c))
    ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} gg' →
        lift (λ c → Endo.mono f (Lift.lower gg' c))
    }

-- RelPreorder-enriched variant (no `Lift` needed for 2-cells).

EndoRelPreorder
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → RP.RelPreorder (lsuc ℓ) ℓ
EndoRelPreorder K =
  record
    { Con = Endo K
    ; _⊑_ = _≤₂_ K
    ; refl = λ {f} → refl₂ K f
    ; trans = λ {f} {g} {h} fg gh → trans₂ K {f = f} {g = g} {h = h} fg gh
    }

EndoRelThin2Cat
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → RelThin2Cat.RelThin2Cat ℓ (lsuc ℓ) ℓ
EndoRelThin2Cat K =
  record
    { Obj = ⊤
    ; Hom = λ _ _ → EndoRelPreorder K
    ; id  = λ {A} → idEndo K
    ; _∘_ = _∘E_
    ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} fg →
        (λ c → fg (Endo.fn g c))
    ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} gg' →
        (λ c → Endo.mono f (gg' c))
    }

module Endo2Cat
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q) where
  private
    C = EndoRelThin2Cat K

  whisker-left
    : {f g h : Endo K}
    → _≤₂_ K f g → _≤₂_ K (h ∘E f) (h ∘E g)
  whisker-left {f} {g} {h} fg =
    RelThin2Cat.whisker-right
      {C = C} {A = tt} {B = tt} {C' = tt}
      {f = h} {g = f} {g' = g}
      fg

  whisker-right
    : {f g h : Endo K}
    → _≤₂_ K f g → _≤₂_ K (f ∘E h) (g ∘E h)
  whisker-right {f} {g} {h} fg =
    RelThin2Cat.whisker-left
      {C = C} {A = tt} {B = tt} {C' = tt}
      {f = f} {f' = g} {g = h}
      fg
