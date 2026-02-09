{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.HeteroInterlinguaCore where

-- Interoperability across *changing* satisfaction relations.
--
-- This development allows two presentations to live over different satisfaction
-- predicates, connected by a satisfaction morphism `SatMor`. The homogeneous
-- specialisation (fixed satisfaction) is provided by `ForPresentations`.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.PresentationCore public using (SatSystem; PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor; SatHom; composeSatMor; idSatMorS)

import LogOS.Minimal.View as View

module For
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
  (m  : SatMor S₁ S₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} S₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} S₂)
  where

  private
    module M  = SatMor m
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    open SatSystem S₁ renaming (Ctx to Ctx₁; Con to Con₁; Sat to Sat₁)
    open SatSystem S₂ renaming (Ctx to Ctx₂; Con to Con₂; Sat to Sat₂)

    Form₁ = P1.Form
    Form₂ = P2.Form

  -- Target satisfaction pulled back along `mapCtx`.
  SatF₂↑ : Ctx₁ → Form₂ → Set ℓSat₂
  SatF₂↑ p φ = P2.SatF (M.mapCtx p) φ

  -- Induced observational relations on target forms (relative to source observers).
  ObsEqF₂↑ : Form₂ → Form₂ → Set (ℓCtx₁ ⊔ ℓSat₂)
  ObsEqF₂↑ = Prop.ObsEqOn SatF₂↑

  Obs≈F₂↑ : Form₂ → Form₂ → Set (ℓCtx₁ ⊔ ℓSat₂)
  Obs≈F₂↑ = View.Obs≈ SatF₂↑

  ObsEqF₂↑↔Obs≈F₂↑ : ∀ {x y} → ObsEqF₂↑ x y ↔ Obs≈F₂↑ x y
  ObsEqF₂↑↔Obs≈F₂↑ {x} {y} = View.ObsEqOn↔Obs≈ SatF₂↑ {x = x} {y = y}

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

  -- Equality on translations: mutual refinement in the observational preorder
  -- induced by the pulled-back target satisfaction (`SatF₂↑`).
  infix 4 _⊑⇒_ _≈⇒_

  _⊑⇒_ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  t ⊑⇒ u = ∀ p φ → SatF₂↑ p (t φ) → SatF₂↑ p (u φ)

  _≈⇒_ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  t ≈⇒ u = (t ⊑⇒ u) × (u ⊑⇒ t)

  -- Presentation alias: pointwise satisfaction equivalence (`↔`) on translations.
  ObsEq⇒ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  ObsEq⇒ t u = ∀ p φ → SatF₂↑ p (t φ) ↔ SatF₂↑ p (u φ)

  ObsEq⇒↔≈⇒ : ∀ {t u} → ObsEq⇒ t u ↔ (t ≈⇒ u)
  ObsEq⇒↔≈⇒ {t} {u} =
    Prop.intro
      (λ eq →
        ( (λ p φ sat → Prop._↔_.to (eq p φ) sat)
        , (λ p φ sat → Prop._↔_.from (eq p φ) sat)
        ))
      (λ (tu , ut) p φ → Prop.intro (tu p φ) (ut p φ))

  -- Named alias: observational equality on translations.
  Trans≈ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  Trans≈ = _≈⇒_

  -- Directional projections (canonical names): mutual refinement splits into the
  -- two entailment directions.
  Trans≈⇒ : ∀ {t u} → Trans≈ t u → (t ⊑⇒ u)
  Trans≈⇒ (tu , _) = tu

  Trans≈⇐ : ∀ {t u} → Trans≈ t u → (u ⊑⇒ t)
  Trans≈⇐ (_ , ut) = ut

  -- Semantics preservation along the satisfaction morphism.
  SemPreserving : (Form₁ → Form₂) → Set _
  SemPreserving t = ∀ p φ → P1.SatF p φ ↔ SatF₂↑ p (t φ)

  abstract
    translate-unique
      : ∀ (t : Form₁ → Form₂)
      → SemPreserving t
      → t ≈⇒ translate
    translate-unique t pres =
      Prop._↔_.to ObsEq⇒↔≈⇒
        (λ p φ →
          Prop.↔-trans (Prop.↔-sym (pres p φ)) (translate-preserves-Sat p φ))

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
    → ObsEqF₂↑ (translate φ) (translate ψ)
  translate-respects-ObsEq {φ} {ψ} eq p =
    let
      tφ : P1.SatF p φ ↔ SatF₂↑ p (translate φ)
      tφ = translate-preserves-Sat p φ
      tψ : P1.SatF p ψ ↔ SatF₂↑ p (translate ψ)
      tψ = translate-preserves-Sat p ψ
    in
    Prop.↔-trans (Prop.↔-sym tφ) (Prop.↔-trans (eq p) tψ)

  -- Derived: translation also respects mutual refinement (the canonical `≈`-shaped form).
  translate-respects-Obs≈
    : ∀ {φ ψ}
    → P1.Obs≈F φ ψ
    → Obs≈F₂↑ (translate φ) (translate ψ)
  translate-respects-Obs≈ {φ} {ψ} eq≈ =
    Prop.to ObsEqF₂↑↔Obs≈F₂↑
      (translate-respects-ObsEq
        (Prop.from (P1.ObsEqF↔Obs≈F {x = φ} {y = ψ}) eq≈))

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

  -- Canonical notion: extensionality w.r.t. observational mutual refinement.
  RespectsObs≈₂↑ : (Con₂ → Con₂) → Set _
  RespectsObs≈₂↑ F = ∀ {c d} → M.Obs≈₂↑ c d → M.Obs≈₂↑ (F c) (F d)

  RespectsObsEq₂↑↔RespectsObs≈₂↑ : ∀ {F} → RespectsObsEq₂↑ F ↔ RespectsObs≈₂↑ F
  RespectsObsEq₂↑↔RespectsObs≈₂↑ {F} =
    Prop.intro
      (λ ext {c} {d} cd≈ →
        Prop._↔_.to M.ObsEq₂↑↔Obs≈₂↑
          (ext (Prop._↔_.from M.ObsEq₂↑↔Obs≈₂↑ cd≈)))
      (λ ext {c} {d} cdEq →
        Prop._↔_.from M.ObsEq₂↑↔Obs≈₂↑
          (ext (Prop._↔_.to M.ObsEq₂↑↔Obs≈₂↑ cdEq)))

  -- Compatibility between side maps, relative to pulled-back observers.
  record Compatible (F₁ : Con₁ → Con₁) (F₂ : Con₂ → Con₂)
    : Set (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₂) where
    field
      commute : ∀ c → Prop.ObsEqOn M.Sat₂↑ (M.mapCon (F₁ c)) (F₂ (M.mapCon c))

  -- Canonical notion: compatibility up to observational mutual refinement.
  Compatible≈ : (Con₁ → Con₁) → (Con₂ → Con₂) → Set (ℓCtx₁ ⊔ ℓCon₁ ⊔ ℓSat₂)
  Compatible≈ F₁ F₂ =
    ∀ c → M.Obs≈₂↑ (M.mapCon (F₁ c)) (F₂ (M.mapCon c))

  Compatible↔Compatible≈ : ∀ {F₁ F₂} → Compatible F₁ F₂ ↔ Compatible≈ F₁ F₂
  Compatible↔Compatible≈ {F₁} {F₂} =
    Prop.intro
      (λ compat c →
        Prop._↔_.to M.ObsEq₂↑↔Obs≈₂↑ (Compatible.commute compat c))
      (λ compat≈ →
        record
          { commute = λ c → Prop._↔_.from M.ObsEq₂↑↔Obs≈₂↑ (compat≈ c)
          })

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

  compatible-comp≈
    : ∀ {F₁ G₁ : Con₁ → Con₁} {F₂ G₂ : Con₂ → Con₂}
    → RespectsObs≈₂↑ F₂
    → Compatible≈ F₁ F₂
    → Compatible≈ G₁ G₂
    → Compatible≈ (λ c → F₁ (G₁ c)) (λ c → F₂ (G₂ c))
  compatible-comp≈ {F₁} {G₁} {F₂} {G₂} extF₂ compatF compatG =
    Prop._↔_.to (Compatible↔Compatible≈ {F₁ = (λ c → F₁ (G₁ c))} {F₂ = (λ c → F₂ (G₂ c))})
      (compatible-comp {F₁ = F₁} {G₁ = G₁} {F₂ = F₂} {G₂ = G₂}
        (Prop._↔_.from (RespectsObsEq₂↑↔RespectsObs≈₂↑ {F = F₂}) extF₂)
        (Prop._↔_.from (Compatible↔Compatible≈ {F₁ = F₁} {F₂ = F₂}) compatF)
        (Prop._↔_.from (Compatible↔Compatible≈ {F₁ = G₁} {F₂ = G₂}) compatG))

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

  ported-closure-naturality≈
    : ∀ (F₁ : Con₁ → Con₁) (F₂ : Con₂ → Con₂)
    → RespectsObs≈₂↑ F₂
    → Compatible≈ F₁ F₂
    → ∀ p (φ : Form₁)
    → SatF₂↑ p (translate (Extend₁ F₁ φ))
        ↔
      SatF₂↑ p (Extend₂ F₂ (translate φ))
  ported-closure-naturality≈ F₁ F₂ ext compat p φ =
    ported-closure-naturality F₁ F₂
      (Prop._↔_.from RespectsObsEq₂↑↔RespectsObs≈₂↑ ext)
      (Prop._↔_.from Compatible↔Compatible≈ compat)
      p φ

-- -------------------------------------------------------------------------
-- Homogeneous (mono) specialisations: the satisfaction relation is fixed.
-- -------------------------------------------------------------------------

-- Canonical presentation: take `Form = Con` and interpret by identity.

canonicalPresentation
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
  → PresentationC {ℓForm = ℓCon} S
canonicalPresentation S =
  let open SatSystem S renaming (Sat to SatC) in
  record
  { Form   = Con
  ; SatF   = SatC
  ; Export = λ x → x
  ; SatC≈F = λ _ _ → Prop.↔-refl
  ; Import = λ x → x
  ; SatF≈C = λ _ _ → Prop.↔-refl
  }

-- Canonical translation along a satisfaction morphism: for canonical
-- presentations, the interlingua translation is exactly `mapCon`.

canonical-translate-along
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ : Level}
    {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
    {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
    (m : SatMor S₁ S₂)
  → let P₁ = canonicalPresentation S₁
        P₂ = canonicalPresentation S₂
        module H = For m P₁ P₂
    in H.translate ≡ SatMor.mapCon m
canonical-translate-along _ = refl

canonical-translate≈mapCon
  : ∀ {ℓCtx₁ ℓCon₁ ℓSat₁ ℓCtx₂ ℓCon₂ ℓSat₂ : Level}
    {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
    {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
    (m : SatMor S₁ S₂)
  → let P₁ = canonicalPresentation S₁
        P₂ = canonicalPresentation S₂
        module H = For m P₁ P₂
    in H._≈⇒_ H.translate (SatMor.mapCon m)
canonical-translate≈mapCon {S₁ = S₁} {S₂ = S₂} m =
  let
    module H = For m (canonicalPresentation S₁) (canonicalPresentation S₂)
  in
  Prop._↔_.to H.ObsEq⇒↔≈⇒
    (λ p c →
      Prop.↔-trans
        (Prop.↔-sym (H.translate-preserves-Sat p c))
        (SatMor.sat-↔ m p c))

module ForPresentations
  {ℓCtx ℓCon ℓSat : Level}
  {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  {ℓForm₁ ℓForm₂ : Level}
  (P₁ : PresentationC {ℓForm = ℓForm₁} S)
  (P₂ : PresentationC {ℓForm = ℓForm₂} S)
  where

  private
    open SatSystem S renaming (Sat to SatC)
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    Form₁ = P1.Form
    Form₂ = P2.Form

    module H = For idSatMorS P₁ P₂

  open H public using
    ( translate
    ; translate-preserves-Sat
    ; _⊑⇒_
    ; _≈⇒_
    ; Trans≈⇒
    ; Trans≈⇐
    ; SemPreserving
    ; translate-unique
    ; translate-respects-ObsEq
    ; translate-respects-Obs≈
    )

  -- Named alias: observational equality on translations (mutual refinement).
  Trans≈ : (Form₁ → Form₂) → (Form₁ → Form₂) → Set _
  Trans≈ = _≈⇒_

  -- Ported closure naturality (homogeneous case): use the heterogeneous theorem
  -- instantiated at the identity satisfaction morphism.
  ported-closure-naturality
    : ∀ (F : Con → Con)
    → P1.RespectsObsEqC F
    → ∀ p (φ : Form₁)
    → P2.SatF p (translate (P1.Extend F φ))
        ↔
      P2.SatF p (P2.Extend F (translate φ))
  ported-closure-naturality F extF p φ =
    H.ported-closure-naturality F F extF compat p φ
    where
      compat : H.Compatible F F
      compat =
        record
          { commute = λ _ _ → Prop.↔-refl
          }

  ported-closure-naturality≈
    : ∀ (F : Con → Con)
    → P1.RespectsObs≈C F
    → ∀ p (φ : Form₁)
    → P2.SatF p (translate (P1.Extend F φ))
        ↔
      P2.SatF p (P2.Extend F (translate φ))
  ported-closure-naturality≈ F extF p φ =
    ported-closure-naturality F
      (Prop._↔_.from (P1.RespectsObsEqC↔RespectsObs≈C {F = F}) extF)
      p φ

-- ---------------------------------------------------------------------------
-- Coherence: identity and composition of canonical translations (homogeneous).
-- ---------------------------------------------------------------------------

translate-id-core
  : ∀ {ℓCtx ℓCon ℓForm ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P : PresentationC {ℓForm = ℓForm} S)
  → ForPresentations._≈⇒_ P P (ForPresentations.translate P P) (λ x → x)
translate-id-core P =
  let module Pm = PresentationC P in
  ( (λ p φ sat → Prop._↔_.from (Pm.Export∘Import≈F p φ) sat)
  , (λ p φ sat → Prop._↔_.to (Pm.Export∘Import≈F p φ) sat)
  )

translate-comp-core
  : ∀ {ℓCtx ℓCon ℓForm₁ ℓForm₂ ℓForm₃ ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P₁ : PresentationC {ℓForm = ℓForm₁} S)
    (P₂ : PresentationC {ℓForm = ℓForm₂} S)
    (P₃ : PresentationC {ℓForm = ℓForm₃} S)
  → ForPresentations._≈⇒_ P₁ P₃
      (ForPresentations.translate P₁ P₃)
      (λ φ → ForPresentations.translate P₂ P₃ (ForPresentations.translate P₁ P₂ φ))
translate-comp-core P₁ P₂ P₃ =
  ( (λ p φ sat →
      Prop._↔_.to (obsEq p φ) sat)
  , (λ p φ sat →
      Prop._↔_.from (obsEq p φ) sat)
  )
  where
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
    module P3 = PresentationC P₃

    obsEq
      : ∀ p φ
      → P3.SatF p (ForPresentations.translate P₁ P₃ φ)
          ↔
        P3.SatF p (ForPresentations.translate P₂ P₃ (ForPresentations.translate P₁ P₂ φ))
    obsEq p φ =
      let
        -- Reduce both sides to `SatC p (Import₁ φ)`, via the intermediate port's roundtrip.
        lhs : P3.SatF p (ForPresentations.translate P₁ P₃ φ) ↔ P1.SatC p (P1.Import φ)
        lhs = Prop.↔-sym (P3.SatC≈F p (P1.Import φ))

        mid : P1.SatC p (P1.Import φ) ↔ P1.SatC p (P2.Import (P2.Export (P1.Import φ)))
        mid = P2.Import∘Export≈C p (P1.Import φ)

        rhs : P1.SatC p (P2.Import (P2.Export (P1.Import φ)))
              ↔ P3.SatF p (ForPresentations.translate P₂ P₃ (ForPresentations.translate P₁ P₂ φ))
        rhs = P3.SatC≈F p (P2.Import (P2.Export (P1.Import φ)))
      in
      Prop.↔-trans lhs (Prop.↔-trans mid rhs)

-- Every presentation is equivalent to the canonical one.

presentation-to-canonical
  : ∀ {ℓCtx ℓCon ℓForm ℓSat : Level}
    {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
    (P : PresentationC {ℓForm = ℓForm} S)
  → let module Sys = SatSystem S
        module Pm = PresentationC P
    in
    (∀ p c → Sys.Sat p c ↔ Sys.Sat p (Pm.Import (Pm.Export c)))
    ×
    (∀ p φ → Pm.SatF p φ ↔ Pm.SatF p (Pm.Export (Pm.Import φ)))
presentation-to-canonical P =
  let module Pm = PresentationC P in
  (Pm.Import∘Export≈C , Pm.Export∘Import≈F)

-- -------------------------------------------------------------------------
-- Composition: heterogeneous canonical translations compose (up to Sat).
-- -------------------------------------------------------------------------

module Compose
  {ℓCtx₁ ℓCon₁ ℓForm₁ ℓSat₁ : Level}
  {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
  {ℓCtx₃ ℓCon₃ ℓForm₃ ℓSat₃ : Level}
  {S₃ : SatSystem {ℓCtx = ℓCtx₃} {ℓCon = ℓCon₃} {ℓSat = ℓSat₃}}
  (m₁ : SatMor S₁ S₂)
  (m₂ : SatMor S₂ S₃)
  (P₁ : PresentationC {ℓForm = ℓForm₁} S₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} S₂)
  (P₃ : PresentationC {ℓForm = ℓForm₃} S₃)
  where

  private
    module H12 = For m₁ P₁ P₂
    module H23 = For m₂ P₂ P₃
    module H13 = For (composeSatMor m₁ m₂) P₁ P₃

  translate-comp
    : H13._≈⇒_ H13.translate (λ φ → H23.translate (H12.translate φ))
  translate-comp =
    let eq = H13.translate-unique _ pres in
    (H13.Trans≈⇐ eq , H13.Trans≈⇒ eq)
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
  {S₁ : SatSystem {ℓCtx = ℓCtx₁} {ℓCon = ℓCon₁} {ℓSat = ℓSat₁}}
  {ℓCtx₂ ℓCon₂ ℓForm₂ ℓSat₂ : Level}
  {S₂ : SatSystem {ℓCtx = ℓCtx₂} {ℓCon = ℓCon₂} {ℓSat = ℓSat₂}}
  (m  : SatHom S₁ S₂)
  (P₁ : PresentationC {ℓForm = ℓForm₁} S₁)
  (P₂ : PresentationC {ℓForm = ℓForm₂} S₂)
  where

  private
    module M  = SatHom m
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    open SatSystem S₁ renaming (Ctx to Ctx₁; Con to Con₁; Sat to Sat₁)
    open SatSystem S₂ renaming (Ctx to Ctx₂; Con to Con₂; Sat to Sat₂)

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
