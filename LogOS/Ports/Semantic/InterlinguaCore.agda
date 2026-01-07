{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.InterlinguaCore where

-- Kernel-independent “interlingua” core:
-- ports over a shared satisfaction relation induce canonical translations,
-- unique up to satisfaction, and closure/normalisation operators commute with
-- these translations once they respect observational equivalence.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.PresentationCore public using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (idSatMor)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero

-- Canonical presentation: take `Form = Con` and interpret by identity.

canonicalPresentation
  : ∀ {ℓCtx ℓCon ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    (SatC : Ctx → Con → Set ℓSat)
  → PresentationC {ℓForm = ℓCon} Ctx Con SatC
canonicalPresentation {Con = Con} SatC = record
  { Form   = Con
  ; SatF   = SatC
  ; Export = λ x → x
  ; SatC≈F = λ _ _ → Prop.↔-refl
  ; Import = λ x → x
  ; SatF≈C = λ _ _ → Prop.↔-refl
  }

module ForPresentations
  {ℓCtx ℓCon ℓSat : Level}
  {Ctx : Set ℓCtx}
  {Con : Set ℓCon}
  {SatC : Ctx → Con → Set ℓSat}
  {ℓForm₁ ℓForm₂ : Level}
  (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC)
  (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC)
  where

  private
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂

    Form₁ = P1.Form
    Form₂ = P2.Form

    module H = Hetero.For (idSatMor SatC) P₁ P₂

  open H public using
    ( translate
    ; translate-preserves-Sat
    ; _≈⇒_
    ; SemPreserving
    ; translate-unique
    ; translate-respects-ObsEq
    )

  -- Named alias: satisfaction-equivalence on translations (pointwise `↔`).
  -- This is the notion used by `translate-unique`.
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
      compat _ _ = Prop.↔-refl

-- ---------------------------------------------------------------------------
-- Coherence: identity and composition of canonical translations.
--
-- These are placed under explicit names to avoid collisions with specialised
-- boundary-level wrappers.
-- ---------------------------------------------------------------------------

translate-id-core
  : ∀ {ℓCtx ℓCon ℓForm ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    (P : PresentationC {ℓForm = ℓForm} Ctx Con SatC)
  → ForPresentations._≈⇒_ {SatC = SatC} P P (ForPresentations.translate P P) (λ x → x)
translate-id-core P p φ =
  let module Pm = PresentationC P
  in Prop.↔-sym (Pm.Export∘Import≈F p φ)

translate-comp-core
  : ∀ {ℓCtx ℓCon ℓForm₁ ℓForm₂ ℓForm₃ ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    (P₁ : PresentationC {ℓForm = ℓForm₁} Ctx Con SatC)
    (P₂ : PresentationC {ℓForm = ℓForm₂} Ctx Con SatC)
    (P₃ : PresentationC {ℓForm = ℓForm₃} Ctx Con SatC)
  → ForPresentations._≈⇒_ {SatC = SatC} P₁ P₃
      (ForPresentations.translate P₁ P₃)
      (λ φ → ForPresentations.translate P₂ P₃ (ForPresentations.translate P₁ P₂ φ))
translate-comp-core {SatC = SatC} P₁ P₂ P₃ p φ =
  let
    module P1 = PresentationC P₁
    module P2 = PresentationC P₂
    module P3 = PresentationC P₃

    -- Reduce both sides to `SatC p (Import₁ φ)`, via the intermediate port's roundtrip.
    lhs : P3.SatF p (ForPresentations.translate P₁ P₃ φ) ↔ SatC p (P1.Import φ)
    lhs = Prop.↔-sym (P3.SatC≈F p (P1.Import φ))

    mid : SatC p (P1.Import φ) ↔ SatC p (P2.Import (P2.Export (P1.Import φ)))
    mid = P2.Import∘Export≈C p (P1.Import φ)

    rhs : SatC p (P2.Import (P2.Export (P1.Import φ)))
          ↔ P3.SatF p (ForPresentations.translate P₂ P₃ (ForPresentations.translate P₁ P₂ φ))
    rhs = P3.SatC≈F p (P2.Import (P2.Export (P1.Import φ)))
  in
  Prop.↔-trans lhs (Prop.↔-trans mid rhs)

-- Every presentation is equivalent to the canonical one.

presentation-to-canonical
  : ∀ {ℓCtx ℓCon ℓForm ℓSat : Level}
    {Ctx : Set ℓCtx}
    {Con : Set ℓCon}
    {SatC : Ctx → Con → Set ℓSat}
    (P : PresentationC {ℓForm = ℓForm} Ctx Con SatC)
  → let module Pm = PresentationC P in
    (∀ p c → SatC p c ↔ SatC p (Pm.Import (Pm.Export c)))
    ×
    (∀ p φ → Pm.SatF p φ ↔ Pm.SatF p (Pm.Export (Pm.Import φ)))
presentation-to-canonical P =
  let module Pm = PresentationC P in
  (Pm.Import∘Export≈C , Pm.Export∘Import≈F)
