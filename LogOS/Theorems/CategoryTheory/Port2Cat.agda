{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Port2Cat where

-- Port/adapter 2-category interface (boundary-level packaging only).

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

record Port2Cat
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  : Set (lsuc (lsuc (ℓ ⊔ ℓForm))) where
  field
    -- Wrapper around the shared `Ref2CatCore` shape.
    core : Wrap.Ref2CatCore (lsuc (ℓ ⊔ ℓForm)) (lsuc (ℓ ⊔ ℓForm)) (ℓ ⊔ ℓForm)
  open Wrap.Ref2CatCore core public

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

  Port2Cat-instance : Port2Cat {ℓ = ℓ} {ℓForm = ℓForm} B
  Port2Cat-instance =
    record
      { core =
          record
            { Obj = Obj
            ; Hom = Hom
            ; _∘_ = λ {P₁} {P₂} {P₃} g f → Interop.composeAdapter B P₁ P₂ P₃ f g
            ; id  = λ {A} → Interop.idAdapter B A
            ; _⇒_ = Adapter⇒
            ; id⇒ = λ {P₁} {P₂} f →
                (λ _ _ sat → sat)
            ; _∙_ = λ {P₁} {P₂} {f} {g} {h} fg gh →
                (λ p φ sat → gh p φ (fg p φ sat))
            ; whiskerL = λ {P₁} {P₂} {P₃} g {f} {f'} ff' p φ sat →
                let
                  left : BoundaryPort.SatF P₂ p (Interop.PortAdapter.map f φ)
                  left =
                    Prop._↔_.from (Interop.PortAdapter.preserves-Sat g p (Interop.PortAdapter.map f φ))
                      sat

                  mid : BoundaryPort.SatF P₂ p (Interop.PortAdapter.map f' φ)
                  mid = ff' p φ left
                in
                Prop._↔_.to (Interop.PortAdapter.preserves-Sat g p (Interop.PortAdapter.map f' φ)) mid
            ; whiskerR = λ {P₁} {P₂} {P₃} {g} {g'} f gg' p φ sat →
                gg' p (Interop.PortAdapter.map f φ) sat
            ; _⊙_ = λ {P₁} {P₂} {P₃} {f} {f'} {g} {g'} ff' gg' p φ sat →
                let
                  step₁ : BoundaryPort.SatF P₃ p (Interop.PortAdapter.map g' (Interop.PortAdapter.map f φ))
                  step₁ = gg' p (Interop.PortAdapter.map f φ) sat

                  back : BoundaryPort.SatF P₂ p (Interop.PortAdapter.map f φ)
                  back =
                    Prop._↔_.from
                      (Interop.PortAdapter.preserves-Sat g' p (Interop.PortAdapter.map f φ))
                      step₁

                  step₂ : BoundaryPort.SatF P₂ p (Interop.PortAdapter.map f' φ)
                  step₂ = ff' p φ back
                in
                Prop._↔_.to
                  (Interop.PortAdapter.preserves-Sat g' p (Interop.PortAdapter.map f' φ))
                  step₂
            }
      }

module ForSystem
  {ℓ : Level}
  {ℓForm : Level}
  (S : System {ℓ = ℓ})
  where

  open System S
  open For {ℓ = ℓ} {ℓForm = ℓForm} {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B public
    using (Port2Cat-instance)
