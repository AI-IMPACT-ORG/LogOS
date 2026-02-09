{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.PortHoCat where

-- Ho-category façade for boundary ports/adapters (up to satisfaction equivalence).

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
open import LogOS.System using (System)

import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Theorems.CategoryTheory.WrapperCore as Wrap

record PortHoCat
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  : Set (lsuc (lsuc (ℓ ⊔ ℓForm))) where
  field
    -- Wrapper around the shared `HoCatCore` shape.
    core : Wrap.HoCatCore (lsuc (ℓ ⊔ ℓForm)) (lsuc (ℓ ⊔ ℓForm)) (ℓ ⊔ ℓForm)
  open Wrap.HoCatCore core public

module For
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  where

  private
    Obj : Set (lsuc (ℓ ⊔ ℓForm))
    Obj = BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B

    Hom : Obj → Obj → Set (lsuc (ℓ ⊔ ℓForm))
    Hom P₁ P₂ = Interop.PortAdapter B P₁ P₂

    Adapter⇒
      : ∀ {P₁ P₂}
      → Hom P₁ P₂ → Hom P₁ P₂ → Set (ℓ ⊔ ℓForm)
    Adapter⇒ {P₁} {P₂} = Interop.For._⊑Adapter_ B P₁ P₂

    adapter⇒-refl : ∀ {P₁ P₂} (A : Hom P₁ P₂) → Adapter⇒ A A
    adapter⇒-refl _ _ _ sat = sat

    adapter⇒-trans
      : ∀ {P₁ P₂} {A B₁ C : Hom P₁ P₂}
      → Adapter⇒ A B₁
      → Adapter⇒ B₁ C
      → Adapter⇒ A C
    adapter⇒-trans ab bc p φ sat = bc p φ (ab p φ sat)

    whiskerL⇒
      : ∀ {P₁ P₂ P₃}
        (g : Hom P₂ P₃)
        {f f' : Hom P₁ P₂}
      → Adapter⇒ f f'
      → Adapter⇒ (Interop.composeAdapter B P₁ P₂ P₃ f g)
                 (Interop.composeAdapter B P₁ P₂ P₃ f' g)
    whiskerL⇒ {P₁} {P₂} {P₃} g {f = f} {f' = f'} ff' p φ sat =
      Prop.to (Interop.PortAdapter.preserves-Sat g p (Interop.PortAdapter.map f' φ))
        (ff' p φ
          (Prop.from (Interop.PortAdapter.preserves-Sat g p (Interop.PortAdapter.map f φ)) sat))

    whiskerR⇒
      : ∀ {P₁ P₂ P₃}
        {g g' : Hom P₂ P₃}
        (f : Hom P₁ P₂)
      → Adapter⇒ g g'
      → Adapter⇒ (Interop.composeAdapter B P₁ P₂ P₃ f g)
                 (Interop.composeAdapter B P₁ P₂ P₃ f g')
    whiskerR⇒ f gg' p φ sat = gg' p (Interop.PortAdapter.map f φ) sat

    comp-mono⇒
      : ∀ {P₁ P₂ P₃}
        {f f' : Hom P₁ P₂}
        {g g' : Hom P₂ P₃}
      → Adapter⇒ f f'
      → Adapter⇒ g g'
      → Adapter⇒ (Interop.composeAdapter B P₁ P₂ P₃ f g)
                 (Interop.composeAdapter B P₁ P₂ P₃ f' g')
    comp-mono⇒ {P₃ = P₃} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg' p φ sat =
      let
        step₁ : BoundaryPort.SatF P₃ p (Interop.PortAdapter.map g' (Interop.PortAdapter.map f φ))
        step₁ = gg' p (Interop.PortAdapter.map f φ) sat
      in
      Prop.to (Interop.PortAdapter.preserves-Sat g' p (Interop.PortAdapter.map f' φ))
        (ff' p φ
          (Prop.from (Interop.PortAdapter.preserves-Sat g' p (Interop.PortAdapter.map f φ)) step₁))

  PortHoCat-instance : PortHoCat {ℓ = ℓ} {ℓForm = ℓForm} B
  PortHoCat-instance =
    record
      { core =
          record
            { Obj = Obj
            ; Hom = Hom
            ; _∘_ = λ {P₁} {P₂} {P₃} g f → Interop.composeAdapter B P₁ P₂ P₃ f g
            ; id  = λ {A} → Interop.idAdapter B A
            ; _⇒_ = Adapter⇒
            ; refl⇒ = λ {P₁} {P₂} f → adapter⇒-refl {P₁ = P₁} {P₂ = P₂} f
            ; trans⇒ = λ {P₁} {P₂} {f} {g} {h} fg gh →
                adapter⇒-trans {P₁ = P₁} {P₂ = P₂} {A = f} {B₁ = g} {C = h} fg gh
            ; whiskerL = λ {P₁} {P₂} {P₃} g {f} {f'} ff' →
                whiskerL⇒ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} g {f = f} {f' = f'} ff'
            ; whiskerR = λ {P₁} {P₂} {P₃} {g} {g'} f gg' →
                whiskerR⇒ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} {g = g} {g' = g'} f gg'
            ; _⊙_ = λ {P₁} {P₂} {P₃} {f} {f'} {g} {g'} ff' gg' →
                comp-mono⇒ {P₁ = P₁} {P₂ = P₂} {P₃ = P₃} {f = f} {f' = f'} {g = g} {g' = g'} ff' gg'
            }
      }

module ForSystem
  {ℓ : Level}
  {ℓForm : Level}
  (S : System {ℓ = ℓ})
  where

  open System S
  open For {ℓ = ℓ} {ℓForm = ℓForm} {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B public
    using (PortHoCat-instance)
