{-
LogOS: an Agda research library for foundational logic system architecture.
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
open import LogOS.Ports.Semantic.SatMor using (SatMor)

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

  translate-unique
    : ∀ (t : Form₁ → Form₂)
    → SemPreserving t
    → t ≈⇒ translate
  translate-unique t pres p φ =
    Prop.↔-trans (Prop.↔-sym (pres p φ)) (translate-preserves-Sat p φ)

  -- Translation respects observational equivalence (relative to pulled-back observers).
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
  Extend₁ = P1.Extend

  Extend₂ : (Con₂ → Con₂) → Form₂ → Form₂
  Extend₂ = P2.Extend

  -- Extensionality of a target endomap, relative to pulled-back observers.
  RespectsObsEq₂↑ : (Con₂ → Con₂) → Set _
  RespectsObsEq₂↑ F = Prop.RespectsObsEqOn M.Sat₂↑ F

  -- Compatibility between side maps, relative to pulled-back observers.
  Compatible
    : (Con₁ → Con₁)
    → (Con₂ → Con₂)
    → Set _
  Compatible F₁ F₂ = ∀ c → Prop.ObsEqOn M.Sat₂↑ (M.mapCon (F₁ c)) (F₂ (M.mapCon c))

  -- Compatibility is closed under composition when the target map respects ObsEq.
  compatible-comp
    : ∀ {F₁ G₁ : Con₁ → Con₁} {F₂ G₂ : Con₂ → Con₂}
    → RespectsObsEq₂↑ F₂
    → Compatible F₁ F₂
    → Compatible G₁ G₂
    → Compatible (λ c → F₁ (G₁ c)) (λ c → F₂ (G₂ c))
  compatible-comp {F₁} {G₁} {F₂} {G₂} extF₂ compatF compatG c =
    let
      step₁ = compatF (G₁ c)
      step₂ = extF₂ (compatG c)
    in
    Prop.ObsEqOn-trans {Sat = M.Sat₂↑} step₁ step₂

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
      lhs₂ = compat (P1.Import φ) p

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
