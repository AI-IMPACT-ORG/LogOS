{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.TranslateHtoW where

-- Basis translation: H ⇒ W (derive whiskering + interchange).

open import LogOS.Prelude
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using (TwoCellOps)
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.PresentationH using
  ( Strict2CatH
  ; Strict2CatHOps
  ; Strict2CatHLaws
  ; Strict2CatH→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.PresentationW using
  ( Strict2CatW
  ; Strict2CatWLaws
  )

Strict2CatH→W
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → Strict2CatH ℓObj ℓHom₁ ℓHom₂
  → Strict2CatW ℓObj ℓHom₁ ℓHom₂
Strict2CatH→W C =
  let
    Ops = Strict2CatH.ops C
    L = Strict2CatH.laws C
    open Strict2CatHOps Ops using (_⊗2_)
  in
  record
    { ops = Strict2CatH→TwoCellOps C
    ; laws =
        let
          -- The W-laws are stated for the derived `TwoCellOps`.
          Derived = Strict2CatH→TwoCellOps C
          open TwoCellOps Derived using (Hom₁; Hom₂; id1; _∘1_; id2; _∙2_; whiskerL2; whiskerR2)
        in
        record
          { id1-left = Strict2CatHLaws.id1-left L
          ; id1-right = Strict2CatHLaws.id1-right L
          ; assoc1 = Strict2CatHLaws.assoc1 L
          ; id2-left = Strict2CatHLaws.id2-left L
          ; id2-right = Strict2CatHLaws.id2-right L
          ; assoc2 = Strict2CatHLaws.assoc2 L
          ; middle4 =
              λ {A} {B} {C₀} {f} {f'} {g} {g'} α β →
                let
                  leftComposite = whiskerR2 {f = g} α ∙2 whiskerL2 {g = f'} β
                  rightComposite = whiskerL2 {g = f} β ∙2 whiskerR2 {f = g'} α

                  leftComposite≡β⊗α : leftComposite ≡ β ⊗2 α
                  leftComposite≡β⊗α =
                    trans
                      (sym (Strict2CatHLaws.⊗2-∙ L (id2 {f = g}) β α (id2 {f = f'})))
                      (cong₂ (_⊗2_) (Strict2CatHLaws.id2-left L β) (Strict2CatHLaws.id2-right L α))

                  rightComposite≡β⊗α : rightComposite ≡ β ⊗2 α
                  rightComposite≡β⊗α =
                    trans
                      (sym (Strict2CatHLaws.⊗2-∙ L β (id2 {f = g'}) (id2 {f = f}) α))
                      (cong₂ (_⊗2_) (Strict2CatHLaws.id2-right L β) (Strict2CatHLaws.id2-left L α))
                in
                trans leftComposite≡β⊗α (sym rightComposite≡β⊗α)
          }
    }

