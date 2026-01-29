{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.HeteroInterlinguaCore where

-- Interoperability across *changing* satisfaction relations.
--
-- Compared to `InterlinguaCore`, this development allows two presentations to
-- live over different satisfaction predicates, connected by a satisfaction
-- morphism `SatMor`.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor; SatHom; composeSatMor)

module For
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {Ctx₁ : Set ℓCtx₁}
  {Con₁ : Set ℓCon₁}
  {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {Ctx₂ : Set ℓCtx₂}
  {Con₂ : Set ℓCon₂}
  {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
  (m  : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
  where

  private
    module M  = SatMor m
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    Form₁ = P1.Form
    Form₂ = P2.Form

  -- Target satisfaction pulled back along `mapCtx`.
  SatF₂↑ : Ctx₁ → Form₂ → Set ℓSat₂
  SatF₂↑ p φ = P2.SatF (M.mapCtx p) φ

  -- Canonical translation (route through constraints, then along `mapCon`).
  translate : Form₁ → Form₂
  translate φ = P2.Export (M.mapCon (P1.Import φ))

  translate-preserves-Sat
    : ∀ p (φ : Form₁)
    → P1.SatF p φ ↔ SatF₂↑ p (translate φ)
  translate-preserves-Sat p φ =
    Prop.↔-trans
      (P1.SatF≈C p φ)
      (Prop.↔-trans (M.sat-↔ p (P1.Import φ)) (P2.SatC≈F (M.mapCtx p) (M.mapCon (P1.Import φ))))

  -- Equality on translations: indistinguishable by the pulled-back target satisfaction.
  infix 4 _≈⇒_
  _≈⇒_ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  t ≈⇒ u = ∀ p φ → SatF₂↑ p (t φ) ↔ SatF₂↑ p (u φ)

  -- Named alias: satisfaction-equivalence on translations.
  Trans≈ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  Trans≈ = _≈⇒_

  -- Semantics preservation along the satisfaction morphism.
  SemPreserving : (Form₁ → Form₂) → Set _
  SemPreserving t = ∀ p φ → P1.SatF p φ ↔ SatF₂↑ p (t φ)

  abstract
    translate-unique
      : ∀ (t : Form₁ → Form₂)
      → SemPreserving t
      → t ≈⇒ translate
    translate-unique t pres p φ =
      Prop.↔-trans (Prop.↔-sym (pres p φ)) (translate-preserves-Sat p φ)

  -- Commuting square: a translation whose semantics commute with the SatMor.
  record CommutingSquare : Set (lsuc (ℓCtx₁ ⊔ ℓCtx₂ ⊔ ℓForm₁ ⊔ ℓForm₂ ⊔ ℓSat₁ ⊔ ℓSat₂)) where
    field
      map : Form₁ → Form₂
      commute : SemPreserving map

  abstract
    canonicalSquare : CommutingSquare
    canonicalSquare =
      record
        { map = translate
        ; commute = translate-preserves-Sat
        }

    square-unique
      : ∀ (S : CommutingSquare)
      → CommutingSquare.map S ≈⇒ translate
    square-unique S =
      translate-unique (CommutingSquare.map S) (CommutingSquare.commute S)

  -- Translation respects observational equality (relative to pulled-back observers).
  translate-respects-ObsEq
    : ∀ {φ ψ}
    → P1.ObsEqF φ ψ
    → ∀ p → SatF₂↑ p (translate φ) ↔ SatF₂↑ p (translate ψ)
  translate-respects-ObsEq {φ} {ψ} eq p =
    let
      tφ : P1.SatF p φ ↔ SatF₂↑ p (translate φ)
      tφ = translate-preserves-Sat p φ
      tψ : P1.SatF p ψ ↔ SatF₂↑ p (translate ψ)
      tψ = translate-preserves-Sat p ψ
    in
    Prop.↔-trans (Prop.↔-sym tφ) (Prop.↔-trans (eq p) tψ)

  -- -------------------------------------------------------------------------
  -- Ported closure naturality (heterogeneous).
  --
  -- Given an endomap on constraints on both sides that is compatible with `mapCon`,
  -- closure commutes with the canonical translation up to satisfaction.
  -- -------------------------------------------------------------------------

  Extend₁ : (Con₁ → Con₁) → Form₁ → Form₁
  Extend₁ =
    let
      module A1 = PresentationC.ExtendAction (P1.extendAction)
    in
    A1.act

  Extend₂ : (Con₂ → Con₂) → Form₂ → Form₂
  Extend₂ =
    let
      module A2 = PresentationC.ExtendAction (P2.extendAction)
    in
    A2.act

  -- Extensionality of a target endomap, relative to pulled-back observers.
  RespectsObsEq₂↑ : (Con₂ → Con₂) → Set _
  RespectsObsEq₂↑ F = Prop.RespectsObsEqOn M.Sat₂↑ F

  -- Compatibility between side maps, relative to pulled-back observers.
  record Compatible (F₁ : Con₁ → Con₁) (F₂ : Con₂ → Con₂)
    : Set (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₂) where
    field
      commute : ∀ c → Prop.ObsEqOn M.Sat₂↑ (M.mapCon (F₁ c)) (F₂ (M.mapCon c))

  -- Compatibility is closed under composition when the target map respects ObsEq.
  compatible-comp
    : ∀ {F₁ G₁ : Con₁ → Con₁} {F₂ G₂ : Con₂ → Con₂}
    → RespectsObsEq₂↑ F₂
    → Compatible F₁ F₂
    → Compatible G₁ G₂
    → Compatible (λ c → F₁ (G₁ c)) (λ c → F₂ (G₂ c))
  compatible-comp {F₁} {G₁} {F₂} {G₂} extF₂ compatF compatG =
    record
      { commute = λ c →
          let
            step₁ = Compatible.commute compatF (G₁ c)
            step₂ = extF₂ (Compatible.commute compatG c)
          in
          Prop.ObsEqOn-trans {Sat = M.Sat₂↑} step₁ step₂
      }

  ported-closure-naturality
    : ∀ (F₁ : Con₁ → Con₁) (F₂ : Con₂ → Con₂)
    → RespectsObsEq₂↑ F₂
    → Compatible F₁ F₂
    → ∀ p (φ : Form₁)
    → SatF₂↑ p (translate (Extend₁ F₁ φ))
        ↔
      SatF₂↑ p (Extend₂ F₂ (translate φ))
  ported-closure-naturality F₁ F₂ extF₂ compat p φ =
    let
      SatF₂-Export : ∀ x → SatF₂↑ p (P2.Export x) ↔ Sat₂ (M.mapCtx p) x
      SatF₂-Export x = Prop.↔-sym (P2.SatC≈F (M.mapCtx p) x)

      -- LHS: translate (Extend₁ F₁ φ) reduces to Sat₂ on `mapCon (F₁ (Import₁ φ))`.
      lhs₀ : SatF₂↑ p (translate (Extend₁ F₁ φ))
             ↔ Sat₂ (M.mapCtx p) (M.mapCon (P1.Import (P1.Export (F₁ (P1.Import φ)))))
      lhs₀ = SatF₂-Export (M.mapCon (P1.Import (P1.Export (F₁ (P1.Import φ)))))

      round₁ : Prop.ObsEqOn Sat₁ (F₁ (P1.Import φ)) (P1.Import (P1.Export (F₁ (P1.Import φ))))
      round₁ q = P1.Import∘Export≈C q (F₁ (P1.Import φ))

      lhs₁ : Sat₂ (M.mapCtx p) (M.mapCon (P1.Import (P1.Export (F₁ (P1.Import φ)))))
             ↔ Sat₂ (M.mapCtx p) (M.mapCon (F₁ (P1.Import φ)))
      lhs₁ =
        let eq₂↑ = M.mapCon-respects-ObsEq round₁ in
        Prop.↔-sym (eq₂↑ p)

      lhs₂ : Sat₂ (M.mapCtx p) (M.mapCon (F₁ (P1.Import φ)))
             ↔ Sat₂ (M.mapCtx p) (F₂ (M.mapCon (P1.Import φ)))
      lhs₂ = Compatible.commute compat (P1.Import φ) p

      -- RHS: Extend₂ uses Import₂; reduce Import₂∘Export₂, then use extensionality.
      rhs₀ : SatF₂↑ p (Extend₂ F₂ (translate φ))
             ↔ Sat₂ (M.mapCtx p) (F₂ (P2.Import (P2.Export (M.mapCon (P1.Import φ)))))
      rhs₀ = SatF₂-Export (F₂ (P2.Import (P2.Export (M.mapCon (P1.Import φ)))))

      round₂ : Prop.ObsEqOn M.Sat₂↑ (P2.Import (P2.Export (M.mapCon (P1.Import φ))))
                                (M.mapCon (P1.Import φ))
      round₂ q = Prop.↔-sym (P2.Import∘Export≈C (M.mapCtx q) (M.mapCon (P1.Import φ)))

      rhs₁ : Sat₂ (M.mapCtx p) (F₂ (P2.Import (P2.Export (M.mapCon (P1.Import φ)))))
             ↔ Sat₂ (M.mapCtx p) (F₂ (M.mapCon (P1.Import φ)))
      rhs₁ = extF₂ round₂ p

      rhs₂ : Sat₂ (M.mapCtx p) (F₂ (M.mapCon (P1.Import φ)))
             ↔ SatF₂↑ p (Extend₂ F₂ (translate φ))
      rhs₂ = Prop.↔-sym (Prop.↔-trans rhs₀ rhs₁)
    in
    Prop.↔-trans (Prop.↔-trans (Prop.↔-trans lhs₀ lhs₁) lhs₂) rhs₂

-- -------------------------------------------------------------------------
-- Composition: heterogeneous canonical translations compose (up to Sat).
-- -------------------------------------------------------------------------

module Compose
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {Ctx₁ : Set ℓCtx₁}
  {Con₁ : Set ℓCon₁}
  {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {Ctx₂ : Set ℓCtx₂}
  {Con₂ : Set ℓCon₂}
  {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
  {ℓCtx₃ ℓCon₃ ℓForm₃ ℓSat₃ : Level}
  {Ctx₃ : Set ℓCtx₃}
  {Con₃ : Set ℓCon₃}
  {Sat₃ : Ctx₃ → Con₃ → Set ℓSat₃}
  (m₁ : SatMor Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
  (m₂ : SatMor Ctx₂ Con₂ Sat₂ Ctx₃ Con₃ Sat₃)
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
  (P₃ : PresentationC {ℓForm = ℓForm₃} Ctx₃ Con₃ Sat₃)
  where

  private
    module H12 = For m₁ P₁ P₂
    module H23 = For m₂ P₂ P₃
    module H13 = For (composeSatMor m₁ m₂) P₁ P₃

  translate-comp
    : H13._≈⇒_ H13.translate (λ φ → H23.translate (H12.translate φ))
  translate-comp =
    λ p φ → Prop.↔-sym (H13.translate-unique _ pres p φ)
    where
      pres : H13.SemPreserving (λ φ → H23.translate (H12.translate φ))
      pres p φ =
        let
          step₁ = H12.translate-preserves-Sat p φ
          step₂ = H23.translate-preserves-Sat (SatMor.mapCtx m₁ p) (H12.translate φ)
        in
        Prop.↔-trans step₁ step₂

-- -------------------------------------------------------------------------
-- Sound interlingua: one-way translations along a satisfaction homomorphism.
-- -------------------------------------------------------------------------

module ForSound
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {Ctx₁ : Set ℓCtx₁}
  {Con₁ : Set ℓCon₁}
  {Sat₁ : Ctx₁ → Con₁ → Set ℓSat₁}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {Ctx₂ : Set ℓCtx₂}
  {Con₂ : Set ℓCon₂}
  {Sat₂ : Ctx₂ → Con₂ → Set ℓSat₂}
  (m  : SatHom Ctx₁ Con₁ Sat₁ Ctx₂ Con₂ Sat₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx₁ Con₁ Sat₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx₂ Con₂ Sat₂)
  where

  private
    module M  = SatHom m
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    Form₁ = P1.Form
    Form₂ = P2.Form

  -- Target satisfaction pulled back along `mapCtx`.
  SatF₂↑ : Ctx₁ → Form₂ → Set ℓSat₂
  SatF₂↑ p φ = P2.SatF (M.mapCtx p) φ

  -- Canonical translation (route through constraints, then along `mapCon`).
  translate : Form₁ → Form₂
  translate φ = P2.Export (M.mapCon (P1.Import φ))

  -- Soundness: translation preserves satisfaction (one-way).
  translate-preserves-Sat
    : ∀ p (φ : Form₁)
    → P1.SatF p φ
    → SatF₂↑ p (translate φ)
  translate-preserves-Sat p φ satF =
    let
      satC : Sat₁ p (P1.Import φ)
      satC = Prop.to (P1.SatF≈C p φ) satF

      sat₂ : Sat₂ (M.mapCtx p) (M.mapCon (P1.Import φ))
      sat₂ = M.sat-→ p (P1.Import φ) satC

      satF₂ : SatF₂↑ p (translate φ)
      satF₂ = Prop.to (P2.SatC≈F (M.mapCtx p) (M.mapCon (P1.Import φ))) sat₂
    in
    satF₂

  -- Semantics preservation along the satisfaction homomorphism.
  SemPreserving : (Form₁ → Form₂) → Set _
  SemPreserving t = ∀ p φ → P1.SatF p φ → SatF₂↑ p (t φ)
